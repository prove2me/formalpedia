-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodPointBranch_consZero_injective_e1881b5a7862
-- name    : P2M_GroundTheory_Heights__Heights_GoodPointBranch_consZero_injective_e1881b5a7862
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:19:04.194901+00:00
-- url     : https://prove2.me/theorems/c7379f0b-baaa-41c9-a484-dc0183e92646
-- title:
--   P2 M Ground Theory Heights  Heights Good Point Branch cons Zero injective e1881b5a7862: P2 M Ground Theory Heights  Heights Good Point Branch cons Zero injective e1881b5a7862
-- statement:
--   The P2 M Ground Theory Heights  Heights Good Point Branch cons Zero injective e1881b5a7862 construction uses the P2 M Ground Theory Heights  Heights Good Point Branch cons Zero injective e1881b5a7862 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GoodPointBranchSlice.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GoodPointBranchSlice.lean#L31-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_NormalModelFibreNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GoodPointBranchSlice
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
open MvPolynomial Filter Topology Matrix ComplexSets Metric Set
noncomputable section
open GroundTheory.Heights₂.Heights.GoodPointBranch

theorem P2M_GroundTheory_Heights__Heights_GoodPointBranch_consZero_injective_e1881b5a7862 {d : ℕ} : Function.Injective (consZero d) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GoodPointBranch».«consZero_injective» := P2M_GroundTheory_Heights__Heights_GoodPointBranch_consZero_injective_e1881b5a7862
