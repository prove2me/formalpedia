-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_covariance_weakStar_unitBall
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.covariance_weakStar_unitBall
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:34:21.314778+00:00
-- url     : https://prove2.me/theorems/d8367bb0-dca4-4f2d-a251-0d93e36052a8
-- title:
--   Lemma 2.2 proof, explicit continuity on the dual unit ball
-- statement:
--   For a Borel centered Gaussian element $W$ in a real separable Banach space $B$, the covariance lift $S:B^*\to H$ is continuous on the closed dual unit ball, from its relative weak-* topology to the Hilbert norm topology:
--   $$S|_{B_1^*}: (B_1^*,w^*)\longrightarrow(H,\|\cdot\|_H)\ \text{is continuous}.$$
--   This is the explicit bounded-restriction assertion in the proof, independent of the defective global lemma.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 5, Lemma 2.2 proof, explicit continuity on the dual unit ball

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

/-- Lemma 2.2 proof, explicit continuity on the dual unit ball, arXiv:0805.3252v1, PDF p.5.
Under U(S l)=A l the H norm topology is exactly the L² topology. No assertion about arbitrary weak-* nets is imported. -/
theorem covariance_weakStar_unitBall
(W : Omega → B) (hW : BorelCenteredGaussianElement P W) :
    @ContinuousOn (B →L[ℝ] ℝ) (L2 P) (dualEvaluationTopology B) inferInstance
      (analysisMap P W) {l : B →L[ℝ] ℝ | ‖l‖ ≤ 1} := by sorry

end BanachResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
