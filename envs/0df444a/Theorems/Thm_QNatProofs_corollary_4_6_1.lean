-- Prove2me | Theorems.Thm_QNatProofs_corollary_4_6_1
-- name    : QNatProofs.corollary_4_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:04:34.581801+00:00
-- url     : https://prove2.me/theorems/bd8a5622-0918-4571-8e9e-1e0d654ab969
-- title:
--   Corollary 4.6.1 — low-depth preparation of the target states
-- statement:
--   There is an absolute constant $c$, and for every QNC$^0$ depth $D$ a depth $D'$, with the following property. Fix sampler parameters $(\mu,K_{\max},q)$ with admissible thresholds, $R=(2K_{\max}+2)q$, a balance threshold $\gamma\in(0,1]$, $H:\{0,1\}^n\to\{0,1\}^R$, and $|\psi_H\rangle=|\psi_{f_H,\gamma}\rangle$ with $f_H=\mathrm{Samp}_{\mathrm{fin}}\circ H$. Suppose $H$ has a nonclean coherent evaluation circuit $U_H\in A_{k_H}CQ$ (depth $D$) for an even $k_H\ge2$, with $S_H$ gates and $R+w_H$ non-input wires. Then for every $\delta_{\mathrm{load}}\in(0,1)$, with $t=\lceil\gamma^{-2}\ln(1/\delta_{\mathrm{load}})\rceil$, there is a circuit in $A_{2k_H+20}CQ$ (depth $D'$) whose reduced output state $\rho_H$ satisfies
--   $$
--   \tfrac12\big\|\rho_H-|\psi_H\rangle\langle\psi_H|\big\|_1\le\delta_{\mathrm{load}},\tag{54}
--   $$
--   with at most $2t(S_H+S_{\mathrm{samp}})+S_{\mathrm{load}}$ gates and at most $t(R+w_H+2q+S_{\mathrm{samp}})+A_{\mathrm{load}}$ non-output wires, where
--   $$
--   S_{\mathrm{samp}}=c\big(K_{\max}^2q^4\log(q+1)+K_{\max}^2q\log(K_{\max}+1)\big),\quad S_{\mathrm{load}}=c\big(tq^2\log(q+1)+t^2\log(t+1)+nt\big),\quad A_{\mathrm{load}}=c\big(tq^2+t^2\log(t+1)+nt\big).
--   $$
--   So a polynomial-size evaluator and polynomially bounded sampler and loader parameters give a polynomial-size preparation circuit with polynomially many ancillas.
--
--   This combines Lemmas 4.4 and 4.6 and is specialized to the PRF in Corollary 4.6.2.
--
--   Differences from the source:
--   - reading: A_kCQ / MH_k (defined in [Par25], not in the paper) → MHLevel k D: C₀Q₁C₁⋯Q_kC_k with Clifford segments C_i of any length and one- and two-qubit unitary segments Q_i of depth ≤ D; reason: the paper's own level counts (p.25: [Cliff][A₄][Cliff][A₄][Cliff] ⊆ A₈; p.40: A₁ = Clifford then QNC⁰) fix this form; A_kCQ ⊆ MH_k on p.22
--   - encoding: A_{k_H}CQ, A_{2k_H+20}CQ with constant depth → MHLevel k_H D and MHLevel (2k_H+20) D', D' depending only on D; reason: constant depth is fixed before the size parameters
--   - reading: If the coherent evaluator for H has polynomial size and uses polynomially many ancilla qubits, and the sampler and loader parameters are polynomially bounded, then the preparation circuit has polynomial size and uses polynomially many ancilla qubits → the quantitative bounds of the proof (p.33): size ≤ 2t(S_H + S_samp) + S_load and non-output wires ≤ t(A_H + A_samp) + A_load, with S_samp, A_samp, S_load, A_load bounded by one absolute constant times the expressions of Lemmas 4.4 and 4.6; reason: for one fixed H 'polynomial size' has no content; the bounds are what the polynomial statement means and what Corollary 4.6.2 uses
--   - encoding: a coherent evaluation circuit U_H, U_H† ∈ A_{k_H}CQ → IsNoncleanEval U_H H on wires x, H(x), workspace, U_H ∈ MHLevel k_H D; reason: the adjoint of a level-k circuit is at level k (the Clifford group is closed under adjoints); the evaluator may leave junk, as in (55)
--   - generalization: the finite Poisson sampler with fixed parameters → any real µ and any admissible thresholds (36); reason: a stronger conclusion
--   - encoding: a designated n-qubit output register; the other qubits traced out → the first n wires; the partial trace over the remaining wires (reducedOutput); reason: any designation is a renaming of wires, which changes neither size nor level
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), Corollary 4.6.1, (54), p.32; proof p.32–33

import Mathlib
import Definitions.Def_QNatProofs_IsAmplitudeOracle
import Definitions.Def_QNatProofs_finPoissonSampler

set_option autoImplicit false

namespace QNatProofs

open QAlgorithms

/-- **Corollary 4.6.1 (Low-depth preparation of the target states)** (Li, Parham, *Natural proofs
for quantum state preparation lower bounds*, arXiv:2610.06826 (held copy sha256 b604fa11…), p.32;
proof p.32–33): "Fix `H : {0,1}ⁿ → {0,1}^R` and let `|ψ_H⟩` be the target state defined above.
Suppose `H` has a coherent evaluation circuit `U_H, U_H† ∈ A_{k_H}CQ` for even `k_H ≥ 2`. Then, for
any error parameter `δ_load ∈ (0, 1)`, there exists a circuit in `A_{2k_H+20}CQ` whose reduced output
state `ρ_H` satisfies `(1/2)‖ρ_H − |ψ_H⟩⟨ψ_H|‖₁ ≤ δ_load`. (54) If the coherent evaluator for `H`
has polynomial size and uses polynomially many ancilla qubits, and the sampler and loader
parameters are polynomially bounded, then the preparation circuit has polynomial size and uses
polynomially many ancilla qubits." The target state is `|ψ_H⟩ = |ψ_{f_H,γ}⟩` ((6), (7)) with
`v_x = Samp_fin(H(x))` for the finite Poisson sampler of §4.1.2 with parameters `(µ, K_max, q)`,
`R = (2K_max + 2)q`, and a fixed balance threshold `γ ∈ (0, 1]` (p.32).

**Formalization Note** `A_kCQ` is `MHLevel k D`; `D'` depends only on `D`. The resource sentence
is stated in the quantitative form of the proof (p.33): with `t = ⌈γ^{-2} ln(1/δ_load)⌉`, the
circuit has at most `2t(S_H + S_samp) + S_load` gates and `t(A_H + A_samp) + A_load` non-output
wires, where `S_H` is the size and `R + w_H` the non-input wire count of `U_H`, `S_samp, A_samp ≤
c(K_max² q⁴ log(q+1) + K_max² q log(K_max+1))` (Lemma 4.4) plus the `2q` output wires of the
sampler, and `S_load ≤ c(tq² log(q+1) + t² log(t+1) + nt)`, `A_load ≤ c(tq² + t² log(t+1) + nt)`
(Lemma 4.6), for one absolute constant `c`. The coherent evaluator is nonclean
(`|x⟩|0⟩|0⟩ ↦ |x⟩|H(x)⟩|junk_x⟩`); its adjoint is then in the same level. The thresholds are any
admissible choice (36). -/
theorem corollary_4_6_1 : ∃ c : ℝ, ∀ D : ℕ, ∃ D' : ℕ,
    ∀ n kH : ℕ, Even kH → 2 ≤ kH →
    ∀ (mu : ℝ) (Kmax q : ℕ) (thr : ℕ → ℕ), AdmissibleThresholds mu Kmax q thr →
    ∀ γ δ : ℝ, 0 < γ → γ ≤ 1 → 0 < δ → δ < 1 →
    ∀ (H : Qubits n → Fin ((2 * Kmax + 2) * q) → Bool) (wH : ℕ)
      (UH : Circuit allGates (n + ((2 * Kmax + 2) * q + wH))),
      UH ∈ MHLevel kH D _ → IsNoncleanEval (r := (2 * Kmax + 2) * q) (w := wH) UH.unitary H →
    ∃ (w : ℕ) (C : Circuit allGates (n + w)), C ∈ MHLevel (2 * kH + 20) D' _ ∧
      ApproxPrepares C
        (psiState (fH (finPoissonSampler Kmax q thr) H) γ : EuclideanSpace ℂ (Qubits n)) δ ∧
      (C.size : ℝ) ≤ 2 * (loadReps γ δ : ℝ) * ((UH.size : ℝ) +
          c * ((Kmax : ℝ) ^ 2 * (q : ℝ) ^ 4 * Real.log ((q : ℝ) + 1) +
            (Kmax : ℝ) ^ 2 * q * Real.log ((Kmax : ℝ) + 1))) +
        c * ((loadReps γ δ : ℝ) * (q : ℝ) ^ 2 * Real.log ((q : ℝ) + 1) +
          (loadReps γ δ : ℝ) ^ 2 * Real.log ((loadReps γ δ : ℝ) + 1) + (n : ℝ) * loadReps γ δ) ∧
      (w : ℝ) ≤ (loadReps γ δ : ℝ) * ((((2 * Kmax + 2) * q + wH : ℕ) : ℝ) + 2 * q +
          c * ((Kmax : ℝ) ^ 2 * (q : ℝ) ^ 4 * Real.log ((q : ℝ) + 1) +
            (Kmax : ℝ) ^ 2 * q * Real.log ((Kmax : ℝ) + 1))) +
        c * ((loadReps γ δ : ℝ) * (q : ℝ) ^ 2 +
          (loadReps γ δ : ℝ) ^ 2 * Real.log ((loadReps γ δ : ℝ) + 1) + (n : ℝ) * loadReps γ δ) := by sorry

end QNatProofs
