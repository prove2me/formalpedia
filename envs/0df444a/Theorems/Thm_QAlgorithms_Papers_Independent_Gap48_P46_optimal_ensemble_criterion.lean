-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P46_optimal_ensemble_criterion
-- name    : QAlgorithms.Papers.Independent.Gap48.P46.optimal_ensemble_criterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:50:50.409777+00:00
-- url     : https://prove2.me/theorems/285ed7c1-5a6b-442c-94b6-520a72e68a71
-- title:
--   Proposition 1: optimal ensemble criterion
-- statement:
--   All quantum systems are nonzero finite-dimensional complex Hilbert spaces. States are positive semidefinite trace-one matrices, and channels are CPTP maps on the full matrix algebra. All entropies and logarithms are in bits. An ensemble is a finite probability distribution of states, with zero weights permitted. For a channel $\Phi$, write $\chi_\Phi(\rho)$ for the maximum ensemble Holevo information at mean $\rho$, $\widehat H_\Phi(\rho)$ for the minimum average output entropy at that mean, and $\overline C(\Phi;\mathcal A)$ for the maximum of $\chi_\Phi$ over a nonempty closed mean constraint $\mathcal A$.
--
--   Let $\mathcal A$ be nonempty, closed and convex. Let $e=\{\pi_i,\rho_i\}$ have mean $\rho_{\rm av}\in\mathcal A$. Write $\chi_\Phi(e)=H(\sum_i\pi_i\Phi(\rho_i))-\sum_i\pi_iH(\Phi(\rho_i))$, and let $D_2$ be quantum relative entropy, taking value $+\infty$ on support violation. Then
--
--   $$e\text{ is optimal}\quad\Longleftrightarrow\quad\sum_j\mu_jD_2(\Phi(\omega_j)\|\Phi(\rho_{\rm av}))\le\chi_\Phi(e)\ \text{for every ensemble }\{\mu_j,\omega_j\}\text{ whose mean lies in }\mathcal A.$$
--
--   Zero-weight distance terms are zero. This criterion tests feasible ensemble averages; individual component states need not lie in the constraint.
-- source:
--   On Shor's channel extension and constrained channels, arXiv:quant-ph/0306196v2, PDF p. 4, Proposition 1: optimal ensemble criterion

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

/-- PDF pp.4–5, Proposition 1: optimality iff the extended distance bound holds for
every ensemble with feasible mean, including components outside the constraint. -/
theorem optimal_ensemble_criterion [Nonempty I] [Nonempty O]
    (Phi : Superop I O) (hPhi : IsChannel Phi) (A : Set (Matrix I I ℂ))
    (hA : Constraint A) (hconvex : Convex ℝ A) (e : Ensemble I) (he : (ensembleAverage e) ∈ A) :
    IsOptimalConstrainedEnsemble Phi A e ↔ ∀ f : Ensemble I, (ensembleAverage f) ∈ A →
      shorEnsembleDistance f Phi (ensembleAverage e) ≤ ENNReal.ofReal (outputHolevo Phi e) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P46

end
