-- Prove2me | Theorems.Thm_QNatProofs_lemma_4_4
-- name    : QNatProofs.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:03:41.306194+00:00
-- url     : https://prove2.me/theorems/5833cb42-fa88-4159-bf2e-8bc412ee85d3
-- title:
--   Lemma 4.4 — coherent finite Poisson sampler in MH (corrected: $K_{\max}\ge1$)
-- statement:
--   There are a QNC$^0$ depth $D$ and an absolute constant $c$ such that for all sampler parameters $\mu$, $K_{\max}\ge1$ and $q$, every admissible threshold choice (36), and $R=(2K_{\max}+2)q$, there is an exact nonclean coherent implementation $U_{\mathrm{samp}}$ of the finite Poisson sampler $\mathrm{Samp}_{\mathrm{fin}}:\{0,1\}^R\to\{0,1\}^{2q}$: for every tape $\Omega\in\{0,1\}^R$,
--   $$
--   U_{\mathrm{samp}}|\Omega\rangle|0^{n_{\mathrm{anc}}}\rangle|0^{2q}\rangle=|\Omega\rangle|\mathrm{junk}_\Omega\rangle|\mathrm{Samp}_{\mathrm{fin}}(\Omega)\rangle,\tag{43}
--   $$
--   the output being $(R_{\mathrm{fin}},\Theta_{\mathrm{fin}})$ with $q$ bits each. $U_{\mathrm{samp}}$ lies in $A_8CQ$, and its size and number of ancillas are at most
--   $$
--   c\,\big(K_{\max}^2q^4\log(q+1)+K_{\max}^2q\log(K_{\max}+1)\big).
--   $$
--
--   This is the low-level circuit for the sampler, used in Lemma 4.1 and Corollary 4.6.1.
--
--   Differences from the source:
--   - correction: Lemma 4.4 for all K_max → hypothesis 1 ≤ K_max; reason: for K_max = 0, q = 1 the bound c(K_max²q⁴log(q+1) + K_max²q log(K_max+1)) is 0, so U_samp would have no gates and leave the output register at 0, but Samp_fin(Ω) = (0, Θ_fin) with Θ_fin = 1 for half the tapes; every other assumption holds
--   - reading: A_kCQ / MH_k (defined in [Par25], not in the paper) → MHLevel k D: C₀Q₁C₁⋯Q_kC_k with Clifford segments C_i of any length and one- and two-qubit unitary segments Q_i of depth ≤ D; reason: the paper's own level counts (p.25: [Cliff][A₄][Cliff][A₄][Cliff] ⊆ A₈; p.40: A₁ = Clifford then QNC⁰) fix this form; A_kCQ ⊆ MH_k on p.22
--   - encoding: A₈CQ ⊆ MH₈ with constant depth; O(·) → MHLevel 8 D for one absolute D; one absolute constant c; reason: constant depth means one D chosen before the parameters
--   - generalization: fixed sampler parameters µ (µ ≥ 1 in §4.1.2), K_max, q and the thresholds of (36) → every real µ and every admissible threshold choice; reason: a stronger conclusion; the thresholds are hard-wired constants
--   - encoding: |Ω⟩|0^{n_anc}⟩|0^{2q}⟩ ↦ |Ω⟩|junk_Ω⟩|Samp_fin(Ω)⟩ → wire order Ω, output (R_fin then Θ_fin), ancillas (IsNoncleanEval); reason: a renaming of wires, which changes neither size nor level
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), Lemma 4.4, (43), p.22; proof p.23–25

import Mathlib
import Definitions.Def_QNatProofs_MHLevel
import Definitions.Def_QNatProofs_finPoissonSampler

set_option autoImplicit false

namespace QNatProofs

open QAlgorithms

/-- **Lemma 4.4 (Coherent implementation of the finite Poisson sampler in MH)** (Li, Parham,
*Natural proofs for quantum state preparation lower bounds*, arXiv:2610.06826 (held copy sha256
b604fa11…), p.22): "Fix sampler parameters `µ`, `K_max`, and `q`, and let `R = (2K_max + 2)q` be the
random-tape length. There exists an exact nonclean coherent implementation `U_samp` for the finite
Poisson sampler `Samp_fin : {0,1}^R → {0,1}^{2q}` defined in Section 4.1.2 that, for every input
tape `Ω ∈ {0,1}^R`, acts in the following form: `U_samp |Ω⟩|0^{n_anc}⟩|0^{2q}⟩ = |Ω⟩|junk_Ω⟩|Samp_fin(Ω)⟩`.
(43) … The circuit `U_samp` lies in `A₈CQ ⊆ MH₈`, and both the circuit size and the number of ancilla
qubits are at most `O(K_max² q⁴ log(q + 1) + K_max² q log(K_max + 1))`."

**Formalization Note** `A₈CQ` is `MHLevel 8 D` for one absolute depth `D`; `O(·)` is one absolute
constant `c`. The sampler uses any admissible thresholds (36) for the Poisson mean `µ`. The output
register (`R_fin` then `Θ_fin`) comes before the workspace (a renaming of wires). The statement
assumes `K_max ≥ 1`: for `K_max = 0` and `q ≥ 1` the bound is `0`, while copying `Θ_fin` to the
output needs a gate. -/
theorem lemma_4_4 : ∃ (D : ℕ) (c : ℝ), ∀ (mu : ℝ) (Kmax q : ℕ) (thr : ℕ → ℕ), 1 ≤ Kmax →
    AdmissibleThresholds mu Kmax q thr →
    ∃ (nanc : ℕ) (U : Circuit allGates ((2 * Kmax + 2) * q + (q + q + nanc))),
      U ∈ MHLevel 8 D _ ∧
      IsNoncleanEval (r := q + q) (w := nanc) U.unitary
        (fun Ω => Fin.append (finPoissonSampler Kmax q thr Ω).1 (finPoissonSampler Kmax q thr Ω).2) ∧
      (U.size : ℝ) ≤ c * ((Kmax : ℝ) ^ 2 * (q : ℝ) ^ 4 * Real.log (q + 1) +
        (Kmax : ℝ) ^ 2 * q * Real.log (Kmax + 1)) ∧
      (nanc : ℝ) ≤ c * ((Kmax : ℝ) ^ 2 * (q : ℝ) ^ 4 * Real.log (q + 1) +
        (Kmax : ℝ) ^ 2 * q * Real.log (Kmax + 1)) := by sorry

end QNatProofs
