-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P46_chi_deficit_bound
-- name    : QAlgorithms.Papers.Independent.Gap48.P46.chi_deficit_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:51:34.68021+00:00
-- url     : https://prove2.me/theorems/73cd3b39-d502-4891-bb06-cf98acaea90d
-- title:
--   Corollary 1: chi-deficit maximal-distance bound
-- statement:
--   All quantum systems are nonzero finite-dimensional complex Hilbert spaces. States are positive semidefinite trace-one matrices, and channels are CPTP maps on the full matrix algebra. All entropies and logarithms are in bits. An ensemble is a finite probability distribution of states, with zero weights permitted. For a channel $\Phi$, write $\chi_\Phi(\rho)$ for the maximum ensemble Holevo information at mean $\rho$, $\widehat H_\Phi(\rho)$ for the minimum average output entropy at that mean, and $\overline C(\Phi;\mathcal A)$ for the maximum of $\chi_\Phi$ over a nonempty closed mean constraint $\mathcal A$.
--
--   Let $\mathcal A$ be nonempty, closed and convex, and let $\rho_{\rm av}$ be the average of an optimal ensemble for $\Phi$ with this constraint. For every $\rho\in\mathcal A$,
--
--   $$\overline C(\Phi;\mathcal A)=\chi_\Phi(\rho_{\rm av})\ge\chi_\Phi(\rho)+D_2(\Phi(\rho)\|\Phi(\rho_{\rm av})).$$
--
--   Here $D_2$ is extended nonnegative relative entropy, infinite on support failure. The inequality bounds the loss in chi by the distance to the optimal output mean.
-- source:
--   On Shor's channel extension and constrained channels, arXiv:quant-ph/0306196v2, PDF p. 6, Corollary 1: chi-deficit maximal-distance bound

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

/-- PDF p.6, Corollary 1: optimal mean capacity and the chi-deficit distance bound.
Convexity is inherited from Proposition 1, which the proof invokes. -/
theorem chi_deficit_bound [Nonempty I] [Nonempty O]
    (Phi : Superop I O) (hPhi : IsChannel Phi) (A : Set (Matrix I I ℂ))
    (hA : Constraint A) (hconvex : Convex ℝ A) (e : Ensemble I) (he : IsOptimalConstrainedEnsemble Phi A e) :
    constrainedChiCapacity Phi A = fixedMeanChi Phi (ensembleAverage e) ∧ ∀ rho ∈ A,
      ENNReal.ofReal (fixedMeanChi Phi rho) + relativeEntropyBits (Phi rho) (Phi (ensembleAverage e)) ≤
        ENNReal.ofReal (constrainedChiCapacity Phi A) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P46

end
