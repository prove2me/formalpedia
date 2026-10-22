-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P46_strict_constraints_suffice
-- name    : QAlgorithms.Papers.Independent.Gap48.P46.strict_constraints_suffice
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:53:06.162038+00:00
-- url     : https://prove2.me/theorems/dbe4d99b-9c3a-4187-9af9-f4c39ae46ec5
-- title:
--   Lemma 2: strict linear constraints suffice
-- statement:
--   All quantum systems are nonzero finite-dimensional complex Hilbert spaces. States are positive semidefinite trace-one matrices, and channels are CPTP maps on the full matrix algebra. All entropies and logarithms are in bits. An ensemble is a finite probability distribution of states, with zero weights permitted. For a channel $\Phi$, write $\chi_\Phi(\rho)$ for the maximum ensemble Holevo information at mean $\rho$, $\widehat H_\Phi(\rho)$ for the minimum average output entropy at that mean, and $\overline C(\Phi;\mathcal A)$ for the maximum of $\chi_\Phi$ over a nonempty closed mean constraint $\mathcal A$. The constraint $\mathcal A\otimes\mathcal B$ includes every joint density with first marginal in $\mathcal A$ and second marginal in $\mathcal B$, including correlated and entangled states.
--
--   Fix channels $\Phi,\Psi$ and a nonempty closed constraint $\mathcal B$ for $\Psi$. Suppose that for every positive semidefinite $A$ and every $\alpha\ge0$ admitting a state $\rho'$ with $\operatorname{Tr}(A\rho')<\alpha$, additivity holds for $\mathcal A_l=\{\rho:\operatorname{Tr}(A\rho)\le\alpha\}$ and $\mathcal B$. Then
--
--   $$\overline C(\Phi\otimes\Psi;\mathcal A\otimes\mathcal B)=\overline C(\Phi;\mathcal A)+\overline C(\Psi;\mathcal B)$$
--
--   for every nonempty closed $\mathcal A$. Strict feasibility is local to each constraint quantified in the premise. This reduces arbitrary closed constraints to strictly feasible linear ones.
-- source:
--   On Shor's channel extension and constrained channels, arXiv:quant-ph/0306196v2, PDF p. 7, Lemma 2: strict linear constraints suffice

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P46

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB)

open QAlgorithms.Papers.Independent.Information100.P08
  (Ensemble ensembleAverage outputHolevo mixedRoof)

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- PDF p.7, Lemma 2: strict feasibility is inside the universal premise. -/
theorem strict_constraints_suffice [Nonempty I] [Nonempty O] [Nonempty J] [Nonempty K]
    (Phi : Superop I O) (Psi : Superop J K) (hPhi : IsChannel Phi) (hPsi : IsChannel Psi)
    (B : Set (Matrix J J ℂ)) (hB : Constraint B)
    (hlinear : ∀ A : Matrix I I ℂ, A.PosSemidef → ∀ alpha : ℝ, 0 ≤ alpha →
      (∃ rho ∈ states I, effectProb A rho < alpha) →
      ConstrainedAdditive Phi Psi (linearConstraint A alpha) B) :
    ∀ A, Constraint A → ConstrainedAdditive Phi Psi A B := by sorry

end QAlgorithms.Papers.Independent.Gap48.P46

end
