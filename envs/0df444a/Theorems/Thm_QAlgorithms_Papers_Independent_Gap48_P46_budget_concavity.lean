-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P46_budget_concavity
-- name    : QAlgorithms.Papers.Independent.Gap48.P46.budget_concavity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:02:54.227363+00:00
-- url     : https://prove2.me/theorems/979923be-1abf-4d0f-829b-6dbb304c2e0c
-- title:
--   §6: budget concavity and equal allocations
-- statement:
--   All quantum systems are nonzero finite-dimensional complex Hilbert spaces. States are positive semidefinite trace-one matrices, and channels are CPTP maps on the full matrix algebra. All entropies and logarithms are in bits. An ensemble is a finite probability distribution of states, with zero weights permitted. For a channel $\Phi$, write $\chi_\Phi(\rho)$ for the maximum ensemble Holevo information at mean $\rho$, $\widehat H_\Phi(\rho)$ for the minimum average output entropy at that mean, and $\overline C(\Phi;\mathcal A)$ for the maximum of $\chi_\Phi$ over a nonempty closed mean constraint $\mathcal A$.
--
--   Let $\Phi$ be a channel and $A\ge0$. Define $D=\{\alpha\ge0:\exists\rho,\ \operatorname{Tr}(A\rho)\le\alpha\}$ and $f(\alpha)=\overline C(\Phi;A,\alpha)$ on $D$, with $\rho$ a density. The function $f$ is nondecreasing and concave on $D$. For every integer $n\ge1$ and $\alpha\in D$,
--
--   $$\max_{\substack{\alpha_i\in D\\\sum_{i=1}^n\alpha_i=n\alpha}}\sum_{i=1}^nf(\alpha_i)=nf(\alpha),$$
--
--   and the equal allocation $\alpha_i=\alpha$ is feasible and attains this value. Concavity is a conclusion, and capacities on empty sections are excluded.
-- source:
--   On Shor's channel extension and constrained channels, arXiv:quant-ph/0306196v2, PDF p. 16, §6: budget concavity and equal allocations

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

/-- PDF p.16, §6 and Appendix II: budget monotonicity, concavity and the allocation
maximum attained at equal budgets, for every positive block length. -/
theorem budget_concavity [Nonempty I] [Nonempty O]
    (Phi : Superop I O) (hPhi : IsChannel Phi) (A : Matrix I I ℂ) (hA : A.PosSemidef) :
    let f := fun alpha => constrainedChiCapacity Phi (linearConstraint A alpha)
    MonotoneOn f (budgetDomain A) ∧ ConcaveOn ℝ (budgetDomain A) f ∧
      ∀ n : ℕ, 1 ≤ n → ∀ alpha ∈ budgetDomain A,
        (fun _ : Fin n => alpha) ∈ blockAllocations A n alpha ∧
        (∑ i : Fin n, f alpha) = (n : ℝ) * f alpha ∧
        MaximizesValue (blockAllocations A n alpha) (fun a => ∑ i, f (a i)) ((n : ℝ) * f alpha) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P46

end
