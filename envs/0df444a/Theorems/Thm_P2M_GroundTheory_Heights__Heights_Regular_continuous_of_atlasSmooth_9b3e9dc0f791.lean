-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_continuous_of_atlasSmooth_9b3e9dc0f791
-- name    : P2M_GroundTheory_Heights__Heights_Regular_continuous_of_atlasSmooth_9b3e9dc0f791
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:18:29.186892+00:00
-- url     : https://prove2.me/theorems/b336b6a4-ab40-4c30-b360-b8538e9b4f1e
-- title:
--   P2 M Ground Theory Heights  Heights Regular continuous of atlas Smooth 9b3e9dc0f791: P2 M Ground Theory Heights  Heights Regular continuous of atlas Smooth 9b3e9dc0f791
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular continuous of atlas Smooth 9b3e9dc0f791 construction uses the P2 M Ground Theory Heights  Heights Regular continuous of atlas Smooth 9b3e9dc0f791 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/IsCompactImageClosureMid.lean#L16-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/IsCompactImageClosureMid.lean#L16-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_BoundedStatements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsCompactImageClosureMid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli shrink regMax tmax)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open ReciprocityTheory.AnForm (levi)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_continuous_of_atlasSmooth_9b3e9dc0f791 {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}
    {f : X → ℝ} (hf : A.Smooth f) : Continuous f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«continuous_of_atlasSmooth» := P2M_GroundTheory_Heights__Heights_Regular_continuous_of_atlasSmooth_9b3e9dc0f791
