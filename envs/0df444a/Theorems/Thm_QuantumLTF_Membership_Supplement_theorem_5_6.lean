-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_theorem_5_6
-- name    : QuantumLTF.Membership.Supplement.theorem_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:49:19.53238+00:00
-- url     : https://prove2.me/theorems/80e0b2ae-579e-435a-8ae8-9c7289ed228e
-- title:
--   Theorem 5.6 — robust gate-efficient pure-state tomography with three $\mathsf{QEX}_M$ queries, success $73/96-\xi$
-- statement:
--   There are universal constants $C,c>0$ such that the following holds for every $n\ge2$, $\epsilon\in(0,1)$, $K\ge Cn/\epsilon^2$ and $M\ge cn^2/\epsilon^2$. There is a tomography procedure which, given a state $\rho_K$ on $(\mathbb C^n)^{\otimes K}$ and followed by three queries to $\mathsf{QEX}_M(f_w,\gamma_n)$, outputs a unit vector $\tilde w\in\mathbb R^n$ such that the following holds for every unit vector $w$ and every $\xi$ with
--   $$\tfrac12\big\|\rho_K-|w\rangle\langle w|^{\otimes K}\big\|_1\le\xi:\qquad(187)$$
--   $$\Pr\big[\|\tilde w-w\|\le\epsilon\big]\ge\frac{73}{96}-\xi .$$
--   The procedure uses $O\big(\frac n{\epsilon^2}\log\frac1\epsilon\,\mathrm{polylog}\,n\big)$ gates and $\mathrm{poly}(n,1/\epsilon)$ classical post-processing time.
--
--   **Formalization Note** $M=2^q$. The procedure is fixed before $w$, $\rho_K$, $\xi$ and the oracle. The gate bound is read as $C'(n/\epsilon^2)(1+\log(1/\epsilon))\log^{K'}n$. The output is the normalized fixed-point vector read from the measured string.
--
--   Differences from the source:
--   - reading: a tomography procedure for ρ_K, introduced after w and ρ_K → one procedure chosen before w, ρ_K, ξ and the oracle (∃ procedure ∀ w ρ ξ U); reason: tomography of an unknown state; this is the stronger order
--   - reading: a state ρ_K on (Cⁿ)^{⊗K}; trace norm → a density matrix on K registers of s qubits supported on the span of the labels i < n (IsStateOnSpan), any s with n ≤ 2^s, followed by e clean ancillas; trace norm traceNorm; reason: Cⁿ embedded in s qubits by binary labels
--   - reading: O((n/ϵ²) log(1/ϵ) polylog n) gates → C'(n/ε²)(1 + log(1/ε))(log n)^{K'} gates over gates12; reason: the literal factor log(1/ε) tends to 0 as ε → 1 while every procedure meeting ‖w̃ − w‖ ≤ ε < 1 for every unit w needs gates; the O(·) is the paper's ε → 0 asymptotics
--   - reading: poly(n, 1/ϵ) classical post-processing time → a reversible circuit over gatesRev (NOT, CNOT, Toffoli) applied to the measured string, of size ≤ C'(n/ε)^{K'}; reason: a reversible circuit permutes basis states, so applying it before the final measurement equals classical post-processing; its size is the time
--   - reading: outputs a unit vector w̃ ∈ ℝⁿ → the output is w̃ := v/‖v‖, with v the fixed-point vector read on designated output wires (readFp); success requires v ≠ 0; reason: a classical machine writes finitely many bits, and a fixed-point vector of norm exactly 1 near a generic w does not exist for n = 2
--   - reading: QEX_M(f_w, γ_n) → the published IsQEX: any unitary U on nq + 1 qubits with U|0…0⟩ the discretized Gaussian example state (M = 2^q, label on the last qubit); the statement holds for every such U; reason: QEX_M is a state-preparation oracle (p. 10): only its action on |0⟩ is specified
--   - encoding: three additional queries → at most three plain uncontrolled calls; reason: a procedure with fewer calls can be padded with unused calls
--   - encoding: M ≥ cn²/ϵ²; universal constants → M = 2^q with 2^q ≥ c n²/ε²; C, c, C', K' fixed before n, ε, K, M; reason: same conditions
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 5.6, Eq. (187), p. 70 (PDF p. 71); proof, pp. 70–72 (PDF pp. 71–73)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_ForwardOnly
import Definitions.Def_QuantumLTF_Membership_Supplement_IsStateOnSpan
import Definitions.Def_QuantumLTF_Membership_Supplement_dirTensorPow
import Definitions.Def_QuantumLTF_Membership_Supplement_padDensity
import Definitions.Def_QuantumLTF_Membership_Supplement_probMixed

namespace QuantumLTF.Membership.Supplement

open QAlgorithms QuantumLTF.Membership QuantumLTF.Example

/-- **Theorem 5.6 (Robust gate-efficient pure-state tomography).** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem 5.6, p. 70
(PDF p. 71): "Assume `n ≥ 2`; the case `n = 1` is trivial. Let `w ∈ Rⁿ` be a unit vector, and let
`ρ_K` be a state on `(Cⁿ)^{⊗K}` satisfying `(1/2)‖ρ_K − |w⟩⟨w|^{⊗K}‖₁ ≤ ξ` (187). There are universal
constants `C, c > 0` such that, for every `ϵ ∈ (0, 1)`, `K ≥ Cn/ϵ²`, and `M ≥ cn²/ϵ²`, there is a
tomography procedure that, followed by three additional queries to `QEX_M(f_w, γ_n)`, outputs a unit
vector `w̃ ∈ Rⁿ` satisfying `‖w̃ − w‖ ≤ ϵ` with probability at least `73/96 − ξ` using
`O((n/ϵ²) log(1/ϵ) polylog n)` gates, together with `poly(n, 1/ϵ)` classical post-processing time."

**Formalization Note.** The procedure is fixed before `w`, `ρ_K`, `ξ` and the oracle (it is tomography
of an unknown state). `M = 2^q`; `QEX_M(f_w, γ_n)` is the published `IsQEX`, and the guarantee holds for
every such unitary. Input: `ρ_K` on `K` registers of `s` qubits, any `s` with `n ≤ 2^s`
(`IsStateOnSpan`), followed by `e` clean ancillas. Quantum part: one `gates12` oracle circuit making at
most three plain queries (not inverse, not controlled), then a computational-basis measurement.
Classical post-processing: a reversible circuit over `gatesRev` (NOT, CNOT, Toffoli) applied to the
measured string, whose size is the post-processing time (equivalently applied coherently before the
measurement, since it permutes basis states). The output is `w̃ := v/‖v‖` with `v` the fixed-point
numbers read on the wires `ov i` (`readFp`); success requires `v ≠ 0` (a fixed-point vector of norm
exactly `1` near a generic `w` does not exist for `n = 2`). Trace norm: the published
`QAlgorithms.traceNorm`. Constants: `C, c` as printed; `C', K'` for the gate bound
`C'(n/ϵ²)(1 + log(1/ϵ))(log n)^{K'}` and the post-processing bound `C'(n/ϵ)^{K'}`, all fixed before
`n, ϵ, K, M`. Reading of `log(1/ϵ)`: `1 + log(1/ϵ)`, since the literal factor tends to `0` as `ϵ → 1`
while every procedure meeting the guarantee must use gates; the `O(·)` is the paper's `ϵ → 0`
asymptotics. -/
theorem theorem_5_6 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ C' : ℝ, 0 < C' ∧ ∃ K' : ℕ,
      ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ K : ℕ, C * n / ε ^ 2 ≤ K → ∀ q : ℕ, c * (n : ℝ) ^ 2 / ε ^ 2 ≤ 2 ^ q →
      ∀ s : ℕ, n ≤ 2 ^ s →
        ∃ (e : ℕ) (cq : OracleCircuit gates12 (fun _ : Fin 1 => n * q + 1) (K * s + e))
          (pp : Circuit gatesRev (K * s + e)) (ℓo fo : ℕ) (ov : Fin n → (Fin ℓo ↪ Fin (K * s + e))),
          Uncontrolled cq ∧ ForwardOnly cq ∧ cq.queryCount 0 ≤ 3 ∧
          (cq.gateCount : ℝ) ≤ C' * (n / ε ^ 2) * (1 + Real.log (1 / ε)) * Real.log n ^ K' ∧
          (pp.size : ℝ) ≤ C' * (n / ε) ^ K' ∧
          ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
          ∀ (ξ : ℝ) (ρ : Matrix (Qubits (K * s)) (Qubits (K * s)) ℂ), IsStateOnSpan n s K ρ →
            traceNorm (ρ - dirTensorPow s K w) / 2 ≤ ξ →
          ∀ U : Matrix (Qubits (n * q + 1)) (Qubits (n * q + 1)) ℂ, IsQEX (q := q) w U →
            open Classical in
            probMixed (pp.unitary * cq.unitary fun _ => U) (padDensity e ρ)
              (fun z =>
                let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun i => readFp (ov i) fo z
                v ≠ 0 ∧ ‖‖v‖⁻¹ • v - w‖ ≤ ε) ≥ 73 / 96 - ξ := by sorry

end QuantumLTF.Membership.Supplement
