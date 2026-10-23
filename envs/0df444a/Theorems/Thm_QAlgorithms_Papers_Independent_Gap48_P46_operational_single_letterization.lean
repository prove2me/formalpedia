-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P46_operational_single_letterization
-- name    : QAlgorithms.Papers.Independent.Gap48.P46.operational_single_letterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:03:34.345514+00:00
-- url     : https://prove2.me/theorems/ea27a8e6-0dbd-4856-86ed-471117e5b330
-- title:
--   §6: block additivity and operational single-letterization
-- statement:
--   All quantum systems are nonzero finite-dimensional complex Hilbert spaces. States are positive semidefinite trace-one matrices, and channels are CPTP maps on the full matrix algebra. All entropies and logarithms are in bits. An ensemble is a finite probability distribution of states, with zero weights permitted. For a channel $\Phi$, write $\chi_\Phi(\rho)$ for the maximum ensemble Holevo information at mean $\rho$, $\widehat H_\Phi(\rho)$ for the minimum average output entropy at that mean, and $\overline C(\Phi;\mathcal A)$ for the maximum of $\chi_\Phi$ over a nonempty closed mean constraint $\mathcal A$.
--
--   Fix a channel $\Phi$, a positive observable $A$, and a feasible nonnegative budget $\alpha$. For $n\ge1$ let $A^{(n)}=\sum_{i=1}^nI^{\otimes(i-1)}\otimes A\otimes I^{\otimes(n-i)}$. Assume the $n$-use weak allocation identity for every $n\ge1$: the block capacity is the attained maximum of $\sum_i\overline C(\Phi;A,\alpha_i)$ over feasible allocations with $\sum_i\alpha_i=n\alpha$. Then
--
--   $$\overline C(\Phi^{\otimes n};A^{(n)},n\alpha)=n\overline C(\Phi;A,\alpha)\quad(n\ge1),\qquad C(\Phi;A,\alpha)=\overline C(\Phi;A,\alpha).$$
--
--   Operational $C$ is the supremum of nonnegative rates achievable by collective block encoders and decoding POVMs with vanishing maximum message error, each codeword satisfying its additive budget. Integer message counts and asymptotic rates in bits are used. It is not defined by the regularization identity cited from [2].
-- source:
--   On Shor's channel extension and constrained channels, arXiv:quant-ph/0306196v2, PDF p. 16, §6: block additivity and operational single-letterization

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

/-- PDF pp.15–16, §6: the conditional n-use weak identity implies block additivity
and single-letter operational capacity. The operational capacity is defined by codes. -/
theorem operational_single_letterization [Nonempty I] [Nonempty O]
    (Phi : Superop I O) (hPhi : IsChannel Phi) (A : Matrix I I ℂ) (hA : A.PosSemidef)
    (alpha : ℝ) (halpha : alpha ∈ budgetDomain A) (hweak : BlockWeak Phi A alpha) :
    (∀ n : ℕ, 1 ≤ n → constrainedChiCapacity (piSuperop (fun _ : Fin n => Phi))
      (linearConstraint (blockObservable A n) ((n : ℝ) * alpha)) =
        (n : ℝ) * constrainedChiCapacity Phi (linearConstraint A alpha)) ∧
    constrainedOperationalCapacity Phi A alpha = constrainedChiCapacity Phi (linearConstraint A alpha) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P46

end
