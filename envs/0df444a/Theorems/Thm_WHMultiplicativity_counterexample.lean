-- Prove2me | Theorems.Thm_WHMultiplicativity_counterexample
-- name    : WHMultiplicativity.counterexample
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:25:20.649488+00:00
-- url     : https://prove2.me/theorems/6ff568d7-8a8f-4b87-bb2c-a05b89486068
-- title:
--   Werner–Holevo counterexample: $\nu_p(S)\,\nu_p(S) < \nu_p(S\otimes S)$ for all $p > p_0 \approx 4.7823$ and for $p = \infty$
-- statement:
--   Let $S$ be the Werner–Holevo map on complex $3\times 3$ matrices,
--
--   $$
--   S(\rho) = \frac12\Big(\operatorname{tr}(\rho)\,\mathbb 1 - \rho^T\Big),
--   $$
--
--   with $\rho^T$ the transpose in the standard basis, and let $\nu_p(\Phi) = \sup_\rho \|\Phi(\rho)\|_p$ be the maximal output $p$-norm, the supremum running over all density matrices $\rho$ of the input space (for $S\otimes S$, all density matrices on $\mathbb C^3\otimes\mathbb C^3$, entangled ones included). Then $S$ is a quantum channel, and there is a number $p_0$ with
--
--   $$
--   4.7823 < p_0 < 4.7824, \qquad \log\frac43 + \frac{1}{p_0}\log\Big(\frac14 + 2^{1-2p_0}\Big) = 0,
--   $$
--
--   such that for every real $p > p_0$, and also for $p = \infty$ (the operator norm), the output-norm sets of $S$ and $S\otimes S$ are bounded above and
--
--   $$
--   \nu_p(S)\,\nu_p(S) < \nu_p(S\otimes S).
--   $$
--
--   Hence the conjecture $\nu_p(S_1\otimes S_2) = \nu_p(S_1)\,\nu_p(S_2)$ for all channels fails with $S_1 = S_2 = S$ for every $p > p_0$ (in particular for $p > 4.79$, as in the abstract) and for $p = \infty$.
--
--   **Formalization Note** $S$ is `WHAdditivity.Renyi.wernerHolevo 3`; $S\otimes S$ is the tensor product of superoperators `QAlgorithms.piSuperop`; $\nu_p$ is `maxOutputNorm`, a real supremum, whence the bounded-above clauses; a real $p$ enters as `ENNReal.ofReal p` and $p = \infty$ as `⊤`.
--
--   Differences from the source:
--   - encoding: conjecture (2) νp(S1 ⊗ S2) = νp(S1)νp(S2) is violated (Δ > 0) → νp(S)·νp(S) < νp(S ⊗ S); reason: the page's violation is Δ(p, Φm) > 0, i.e. νp(S ⊗ S) ≥ ‖S ⊗ S(|Φm⟩⟨Φm|)‖_p > νp(S)²; the strict inequality is the negation of (2) in the only direction that can fail
--   - reading: the zero p0 is numerically determined as p0 = 4.7823 → p0 is a zero of log(4/3) + (1/p0) log(1/4 + 2^{1−2p0}) with 4.7823 < p0 < 4.7824; reason: the printed value is the four-decimal truncation of the zero 4.782311…; the bracket together with the equation pins p0, which is the stronger reading
--   - generalization: νp as a supremum → additional conclusions BddAbove for the output-norm sets of S and S ⊗ S; reason: extra conclusions that make the suprema genuine
--   - encoding: S a channel (the conjecture is for channels) → the clause QAlgorithms.IsChannel (wernerHolevo 3); reason: Kraus form = CPTP in finite dimension
--   - encoding: S ⊗ S on ℂ^d ⊗ ℂ^d → QAlgorithms.piSuperop (fun _ : Fin 2 => S) on matrices indexed by Fin 2 → Fin d; reason: the tensor product of superoperators through matrix units, on every input (entangled ones included); y : Fin 2 → Fin d is the basis vector |y 0⟩ ⊗ |y 1⟩
--   - encoding: ν_p(S) = sup over all input density operators of ‖S(ρ)‖_p → maxOutputNorm p S, the real sSup of outputNorms p S over every density matrix; reason: same supremum; the BddAbove clauses rule out Lean's junk value of sSup
--   - encoding: ‖X‖_p = (tr|X|^p)^{1/p} for real p, and ‖·‖_∞ the operator norm → schattenNorm p X with p : ℝ≥0∞, a real p entering as ENNReal.ofReal p and ∞ as ⊤; reason: tr|X|^p = tr (XᴴX)^{p/2}; ⊤ gives the ℓ² operator norm; same values
--   - encoding: matrix transpose and conjugates with respect to some fixed basis → the standard basis of ℂ^d (index Fin d); reason: any fixed basis; the statement is the same up to a unitary change of basis
-- source:
--   Werner and Holevo, Counterexample to an additivity conjecture for output purity of quantum channels, arXiv:quant-ph/0203003v1, §II, p.2 (claims after eq. (13)); abstract, p.1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_WHAdditivity_Renyi_Model
import Definitions.Def_WHMultiplicativity_outputNorms
import Definitions.Def_WHMultiplicativity_maxOutputNorm

open scoped ENNReal
open WHAdditivity.Renyi

namespace WHMultiplicativity

/-- Werner and Holevo, *Counterexample to an additivity conjecture for output purity of quantum
channels*, arXiv:quant-ph/0203003v1, §II, p.2 (after eq. (13)), and abstract, p.1: the channel
`S(ρ) = (tr(ρ)𝟙 − ρᵀ)/2` on `3 × 3` matrices violates the multiplicativity conjecture (2),
`ν_p(S₁ ⊗ S₂) = ν_p(S₁) ν_p(S₂)`, with `S₁ = S₂ = S`, for every `p > p₀` and for `p = ∞`:
`S` is a channel, and there is `p₀` (the zero of (13), `4.7823 < p₀ < 4.7824`) such that
`ν_p(S) ν_p(S) < ν_p(S ⊗ S)` for every real `p > p₀` and for `p = ∞`.

**Formalization Note.** `S = wernerHolevo 3` (the paper's (6) with `d = 3`, in the standard
basis); `S ⊗ S = QAlgorithms.piSuperop (fun _ : Fin 2 => S)` on `ℂ³ ⊗ ℂ³` (index
`Fin 2 → Fin 3`); `ν_p = maxOutputNorm`, the supremum of `‖Φ(ρ)‖_p` over **all** density matrices
of the input space (for `S ⊗ S`, entangled ones included); `‖·‖_p = schattenNorm`, with a real
`p` entering as `ENNReal.ofReal p` and `p = ∞` as `⊤` (operator norm). Each clause also asserts
that the output-norm sets are bounded above, so the suprema are genuine. `p₀` is pinned as the zero
of the closed form (13), `log(4/3) + (1/p₀) log(1/4 + 2^{1−2p₀}) = 0`, inside the bracket given by
the printed value `p₀ = 4.7823`. -/
theorem counterexample :
    QAlgorithms.IsChannel (wernerHolevo 3) ∧
      ∃ p0 : ℝ, 4.7823 < p0 ∧ p0 < 4.7824 ∧
        Real.log (4 / 3) + (1 / p0) * Real.log (1 / 4 + (2 : ℝ) ^ (1 - 2 * p0)) = 0 ∧
        (∀ p : ℝ, p0 < p →
          BddAbove (outputNorms (ENNReal.ofReal p) (wernerHolevo 3)) ∧
            BddAbove (outputNorms (ENNReal.ofReal p)
              (QAlgorithms.piSuperop (fun _ : Fin 2 => wernerHolevo 3))) ∧
            maxOutputNorm (ENNReal.ofReal p) (wernerHolevo 3) *
                maxOutputNorm (ENNReal.ofReal p) (wernerHolevo 3) <
              maxOutputNorm (ENNReal.ofReal p)
                (QAlgorithms.piSuperop (fun _ : Fin 2 => wernerHolevo 3))) ∧
        (BddAbove (outputNorms ⊤ (wernerHolevo 3)) ∧
          BddAbove (outputNorms ⊤ (QAlgorithms.piSuperop (fun _ : Fin 2 => wernerHolevo 3))) ∧
          maxOutputNorm ⊤ (wernerHolevo 3) * maxOutputNorm ⊤ (wernerHolevo 3) <
            maxOutputNorm ⊤ (QAlgorithms.piSuperop (fun _ : Fin 2 => wernerHolevo 3))) := by sorry

end WHMultiplicativity
