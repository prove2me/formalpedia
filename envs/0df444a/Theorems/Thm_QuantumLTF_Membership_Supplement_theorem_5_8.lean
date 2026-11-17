-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_theorem_5_8
-- name    : QuantumLTF.Membership.Supplement.theorem_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:49:43.666288+00:00
-- url     : https://prove2.me/theorems/8cff151f-8043-4ba0-869f-f766fb0e7e72
-- title:
--   Theorem 5.8 — learning homogeneous LTFs from $\mathsf{QEX}_M$ with $O(n^{1/4}/\sqrt\epsilon)$ queries
-- statement:
--   Let $n\ge2$, let $f_w(x)=\mathrm{sign}(\langle w,x\rangle)$ for $w\in\mathbb S^{n-1}$, and let $\epsilon\in(0,1/2)$. Set
--   $$K=\lceil c_1n/\epsilon^2\rceil,\qquad D=2K+1,\qquad M=2^{\lceil\log_2(c_2n^{13/4}K^{49/16})\rceil},$$
--   where $c_1,c_2>0$ are sufficiently large universal constants. Given coherent access to $\mathsf{QEX}_M(f_w,\gamma_n)$ and its inverse, there is a quantum algorithm that outputs a unit vector $\tilde w\in\mathbb R^n$ with
--   $$\|\tilde w-w\|\le\epsilon$$
--   with probability at least $2/3$. The algorithm makes $O(n^{1/4}/\sqrt\epsilon)$ queries to $\mathsf{QEX}_M(f_w,\gamma_n)$ and its inverse, uses $\tilde O(n^{5/4}/\sqrt\epsilon+n/\epsilon^2)$ additional gates ($\tilde O$ hides factors polylogarithmic in $n$ and $1/\epsilon$), and $\mathrm{poly}(n,1/\epsilon)$ classical post-processing time.
--
--   **Formalization Note** One oracle circuit, fixed before $w$ and the oracle, followed by a computational-basis measurement and reversible classical post-processing.
--
--   Differences from the source:
--   - reading: c1, c2 > 0 sufficiently large universal constants → ∃ c1₀, c2₀ > 0, ∀ c1 ≥ c1₀, ∀ c2 ≥ c2₀, ∃ C, K' (the hidden constants may depend on c1, c2); reason: the stronger of the two readings ('there exist c1, c2' would be weaker)
--   - reading: a quantum algorithm with coherent access to QEX_M and its inverse → one oracle circuit over gates12 from |0…0⟩ with uncontrolled plain or inverse calls (counted together), measured in the computational basis at the end; reason: the algorithm's mid-circuit measurements (Theorems 5.3, 5.4) are deferred to the end; this is the unitary model
--   - reading: QEX_M(f_w, γ_n) → the published IsQEX: any unitary U on nq + 1 qubits with U|0…0⟩ the discretized Gaussian example state (M = 2^q, label on the last qubit); the statement holds for every such U; reason: QEX_M is a state-preparation oracle (p. 10): only its action on |0⟩ is specified
--   - reading: outputs a unit vector w̃ ∈ ℝⁿ → the output is w̃ := v/‖v‖, with v the fixed-point vector read on designated output wires (readFp); success requires v ≠ 0; reason: a classical machine writes finitely many bits, and a fixed-point vector of norm exactly 1 near a generic w does not exist for n = 2
--   - reading: poly(n, 1/ϵ) classical post-processing time → a reversible circuit over gatesRev (NOT, CNOT, Toffoli) applied to the measured string, of size ≤ C'(n/ε)^{K'}; reason: a reversible circuit permutes basis states, so applying it before the final measurement equals classical post-processing; its size is the time
--   - encoding: M := 2^{⌈log2(c2 n^{13/4} K^{49/16})⌉}; Õ(n^{5/4}/√ϵ + n/ϵ²); poly(n, 1/ϵ) → q := ⌈log₂(c2 n^{13/4} K^{49/16})⌉₊; C (n^{5/4}/√ε + n/ε²) log^{K'}(n/ε); C (n/ε)^{K'}; D does not appear; reason: same quantities; log natural
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 5.8, p. 72 (PDF p. 73); also Theorem 1.3, p. 14 (PDF p. 15)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Example_qex

namespace QuantumLTF.Membership.Supplement

open QAlgorithms QuantumLTF.Membership QuantumLTF.Example

/-- **Theorem 5.8 (Learning homogeneous LTFs with Example Oracle).** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem 5.8, p. 72
(PDF p. 73), also Theorem 1.3: "Assume `n ≥ 2` … Let `f_w(x) := sign(⟨w, x⟩)` for some `w ∈ S^{n−1}`,
and let `ϵ ∈ (0, 1/2)`. Set `K := ⌈c1 n/ϵ²⌉`, `D := 2K + 1`, and `M := 2^{⌈log2(c2 n^{13/4} K^{49/16})⌉}`,
where `c1, c2 > 0` are sufficiently large universal constants. Given coherent access to `QEX_M(f_w, γ_n)`
and its inverse, there exists a quantum algorithm that outputs a unit vector `w̃ ∈ Rⁿ` such that
`‖w̃ − w‖ ≤ ϵ` with probability at least `2/3`. The algorithm makes `O(n^{1/4}/√ϵ)` queries to
`QEX_M(f_w, γ_n)` and its inverse, using `Õ(n^{5/4}/√ϵ + n/ϵ²)` additional gates, where the `Õ`
notation hides factors polylogarithmic in `n` and `1/ϵ`, together with `poly(n, 1/ϵ)` classical
post-processing time."

**Formalization Note.** "Sufficiently large universal constants": there are `c1₀, c2₀ > 0` such that
the statement holds for all `c1 ≥ c1₀`, `c2 ≥ c2₀` (the hidden constants `C, K'` may depend on `c1, c2`).
`M = 2^q` with `q = ⌈log₂(c2 n^{13/4} K^{49/16})⌉`; `D` does not appear in the conclusion.
`QEX_M(f_w, γ_n)` is the published `IsQEX` (every such unitary). The algorithm is one `gates12` oracle
circuit, fixed before `w` and the oracle, from `|0…0⟩`, with plain and inverse calls (counted together,
uncontrolled), measured in the computational basis; classical post-processing is a `gatesRev`
circuit applied to the measured string (its size is the post-processing time); the output is
`w̃ := v/‖v‖` with `v` the fixed-point vector read on the wires `ov` (`v ≠ 0` required). `Õ`: a factor
`log^{K'}(n/ϵ)`; `poly(n, 1/ϵ)`: `C (n/ϵ)^{K'}`. -/
theorem theorem_5_8 :
    ∃ c1₀ c2₀ : ℝ, 0 < c1₀ ∧ 0 < c2₀ ∧ ∀ c1 c2 : ℝ, c1₀ ≤ c1 → c2₀ ≤ c2 →
      ∃ (C : ℝ) (K' : ℕ), 0 < C ∧
        ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
          let K : ℕ := ⌈c1 * n / ε ^ 2⌉₊
          let q : ℕ := ⌈Real.logb 2 (c2 * (n : ℝ) ^ (13 / 4 : ℝ) * (K : ℝ) ^ (49 / 16 : ℝ))⌉₊
          ∃ (m : ℕ) (cq : OracleCircuit gates12 (fun _ : Fin 1 => n * q + 1) m) (pp : Circuit gatesRev m)
            (ℓo fo : ℕ) (ov : Fin n → (Fin ℓo ↪ Fin m)),
            Uncontrolled cq ∧
            (cq.queryCount 0 : ℝ) ≤ C * (n : ℝ) ^ (1 / 4 : ℝ) / Real.sqrt ε ∧
            (cq.gateCount : ℝ) ≤
              C * ((n : ℝ) ^ (5 / 4 : ℝ) / Real.sqrt ε + n / ε ^ 2) * Real.log (n / ε) ^ K' ∧
            (pp.size : ℝ) ≤ C * (n / ε) ^ K' ∧
            ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
            ∀ U : Matrix (Qubits (n * q + 1)) (Qubits (n * q + 1)) ℂ, IsQEX (q := q) w U →
              open Classical in
              probEvent (act (pp.unitary * cq.unitary fun _ => U) (zeroKet m))
                (fun z =>
                  let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun i => readFp (ov i) fo z
                  v ≠ 0 ∧ ‖‖v‖⁻¹ • v - w‖ ≤ ε) ≥ 2 / 3 := by sorry

end QuantumLTF.Membership.Supplement
