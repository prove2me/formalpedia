-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P02_iid_additivity_and_condition
-- name    : QAlgorithms.Papers.Independent.Bridge50.P02.iid_additivity_and_condition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:50:34.339136+00:00
-- url     : https://prove2.me/theorems/2a64511c-8541-41b8-bfde-a8476205da5c
-- title:
--   Unnumbered IID example: additive entropy, variance and analytic condition
-- statement:
--   Let $\rho,\sigma$ be faithful density matrices on a nonzero finite-dimensional complex Hilbert space. Set $\rho_n=\rho^{\otimes n}$ and $\sigma_n=\sigma^{\otimes n}$ for $n\ge1$, and take $w_n=n$. In natural logarithms,
--   $$D(\rho_n\Vert\sigma_n)=nD(\rho\Vert\sigma),\qquad V(\rho_n\Vert\sigma_n)=nV(\rho\Vert\sigma),\qquad\Psi_s(\rho_n\mid\sigma_n)=n\Psi_s(\rho\mid\sigma).$$
--   Consequently Condition 1 holds and the computed rates satisfy $d=D(\rho\Vert\sigma)$ and $v=V(\rho\Vert\sigma)$. The entropy correction vanishes identically.
--
--   This verifies that the main analytic framework contains the general finite-dimensional IID example, including equal densities.
-- source:
--   Second-order asymptotics for quantum hypothesis testing in settings beyond i.i.d. - quantum lattice systems and more, arXiv:1510.04682v4, PDF p. 16, Unnumbered IID example

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P02

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P02

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15
  (evaluate positiveMatrixRpow modularMatrix modularQuadratic resolventOverlap petzOverlap
    finiteRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower testingBeta)

open QAlgorithms.Papers.Independent.Information100.P58 (normalQuantile)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Unnumbered IID example, PDF p.16: additivity, the two computed rates,
Petz-log scaling, Condition 1, and zero entropy correction. -/
theorem iid_additivity_and_condition [Nonempty I] (rho sigma : Mat I)
    (hrho : QAlgorithms.IsDensityMatrix rho) (hsigma : QAlgorithms.IsDensityMatrix sigma)
    (hfaithfulRho : rho.PosDef) (hfaithfulSigma : sigma.PosDef) :
    (∀ n : ℕ, 1 ≤ n →
      finitePairRelativeEntropyNats (tensorPower n rho) (tensorPower n sigma) = (n : ℝ) * finitePairRelativeEntropyNats rho sigma ∧
      pairInformationVarianceNats (tensorPower n rho) (tensorPower n sigma) =
        (n : ℝ) * pairInformationVarianceNats rho sigma ∧
      ∀ s : ℝ, realPetzLogOverlap (tensorPower n rho) (tensorPower n sigma) s = (n : ℝ) * realPetzLogOverlap rho sigma s) ∧
    relativeEntropyRate (iidSequence rho sigma) iidWeight = finitePairRelativeEntropyNats rho sigma ∧
    varianceRate (iidSequence rho sigma) iidWeight = pairInformationVarianceNats rho sigma ∧
    ConditionOne (iidSequence rho sigma) iidWeight ∧
    (∀ k, relativeEntropyCorrection (iidSequence rho sigma) iidWeight k = 0) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P02

end
