-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P46_strong_implies_weak
-- name    : QAlgorithms.Papers.Independent.Gap48.P46.strong_implies_weak
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:01:47.612405+00:00
-- url     : https://prove2.me/theorems/bc39132c-4cd7-421b-8931-0ff20f5fefcb
-- title:
--   §6: constrained additivity implies weak additivity
-- statement:
--   All quantum systems are nonzero finite-dimensional complex Hilbert spaces. States are positive semidefinite trace-one matrices, and channels are CPTP maps on the full matrix algebra. All entropies and logarithms are in bits. An ensemble is a finite probability distribution of states, with zero weights permitted. For a channel $\Phi$, write $\chi_\Phi(\rho)$ for the maximum ensemble Holevo information at mean $\rho$, $\widehat H_\Phi(\rho)$ for the minimum average output entropy at that mean, and $\overline C(\Phi;\mathcal A)$ for the maximum of $\chi_\Phi$ over a nonempty closed mean constraint $\mathcal A$.
--
--   Fix channels $\Phi,\Psi$ satisfying additivity for every feasible positive-observable linear constraint pair. Let $A,B\ge0$, and let $\gamma\ge0$ be feasible for the total observable $A\otimes I+I\otimes B$. Then
--
--   $$\overline C(\Phi\otimes\Psi;A\otimes I+I\otimes B,\gamma)=\max_{\substack{\alpha,\beta\ge0,\ \alpha+\beta=\gamma\\\alpha,\beta\text{ individually feasible}}}[\overline C(\Phi;A,\alpha)+\overline C(\Psi;B,\beta)].$$
--
--   The allocation maximum is attained. Here a capacity with an observable and budget uses the inequality $\operatorname{Tr}(A\rho)\le\alpha$. This is the local conditional implication from strong to weak additivity.
-- source:
--   On Shor's channel extension and constrained channels, arXiv:quant-ph/0306196v2, PDF p. 15, §6: constrained additivity implies weak additivity

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

/-- PDF pp.15–16, §6: strong linear-constraint additivity implies weak allocation
additivity, with a feasible maximizing allocation. -/
theorem strong_implies_weak [Nonempty I] [Nonempty O] [Nonempty J] [Nonempty K]
    (Phi : Superop I O) (Psi : Superop J K) (hPhi : IsChannel Phi) (hPsi : IsChannel Psi)
    (h : LinearAdditive Phi Psi) (A : Matrix I I ℂ) (B : Matrix J J ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (gamma : ℝ)
    (hgamma : gamma ∈ budgetDomain (sumObservable A B)) : WeakAt Phi Psi A B gamma := by sorry

end QAlgorithms.Papers.Independent.Gap48.P46

end
