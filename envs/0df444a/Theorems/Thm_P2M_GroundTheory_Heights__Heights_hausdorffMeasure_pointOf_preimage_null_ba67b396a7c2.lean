-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_hausdorffMeasure_pointOf_preimage_null_ba67b396a7c2
-- name    : P2M_GroundTheory_Heights__Heights_hausdorffMeasure_pointOf_preimage_null_ba67b396a7c2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:46:54.208622+00:00
-- url     : https://prove2.me/theorems/4f201d93-913f-4bc8-bbe3-b014f592a192
-- title:
--   P2 M Ground Theory Heights  Heights hausdorff Measure point Of preimage null ba67b396a7c2: P2 M Ground Theory Heights  Heights hausdorff Measure point Of preimage null ba67b396a7c2
-- statement:
--   The P2 M Ground Theory Heights  Heights hausdorff Measure point Of preimage null ba67b396a7c2 construction uses the P2 M Ground Theory Heights  Heights hausdorff Measure point Of preimage null ba67b396a7c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeTangentDim.lean#L26-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeTangentDim.lean#L26-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeKrullDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameJacobianGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_hausdorffMeasure_pointOf_preimage_null_ba67b396a7c2 (h : HermNorm n) {d : ℝ} (hd : 0 ≤ d)
    {S : Set (EuclideanSpace ℂ (Fin n))} (hS : μH[d] S = 0) :
    μH[d] {y | WithLp.toLp 2 (h.pointOf y) ∈ S} = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«hausdorffMeasure_pointOf_preimage_null» := P2M_GroundTheory_Heights__Heights_hausdorffMeasure_pointOf_preimage_null_ba67b396a7c2
