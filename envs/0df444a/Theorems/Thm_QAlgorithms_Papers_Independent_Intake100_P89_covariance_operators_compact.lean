-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_covariance_operators_compact
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.covariance_operators_compact
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:36:10.034164+00:00
-- url     : https://prove2.me/theorems/a5f92030-ec71-4bb6-9b7b-75976ac66a21
-- title:
--   Lemma 2.4: compact covariance and synthesis operators
-- statement:
--   For a Borel centered Gaussian element $W$ of a real separable Banach space $B$, define $A\ell=\ell(W)\in L^2(P)$, $A^*H=E[HW]\in B$, and $S\ell=E[W\ell(W)]$. Then
--   $$A^*:L^2(P)\to B,\qquad A:B^*\to L^2(P),\qquad S:B^*\to B$$
--   are compact for the norm topologies. In particular, compactness of synthesis is into the ambient Banach space, without assuming reflexivity.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 6, Lemma 2.4: compact covariance and synthesis operators

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P89

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P89

universe u v w

variable {Omega : Type u} [MeasurableSpace Omega]

section BanachResults

variable {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]

variable [hComplete : CompleteSpace B] [hSeparable : TopologicalSpace.SeparableSpace B]

variable (P : Measure Omega) [hP : IsProbabilityMeasure P]

include hP hComplete hSeparable

/-- Lemma 2.4: compact covariance and synthesis operators, arXiv:0805.3252v1, PDF p.6.
Compact means the closure of the image of each bounded set is compact, exactly the source norm notion. -/
theorem covariance_operators_compact
(W : Omega → B) (hW : BorelCenteredGaussianElement P W) :
    NormCompact (synthesis P W) ∧ NormCompact (analysisMap P W) ∧
      NormCompact (covarianceMap P W) := by sorry

end BanachResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
