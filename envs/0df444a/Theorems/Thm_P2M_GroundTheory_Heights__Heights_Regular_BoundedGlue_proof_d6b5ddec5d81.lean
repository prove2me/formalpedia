-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_BoundedGlue_proof_d6b5ddec5d81
-- name    : P2M_GroundTheory_Heights__Heights_Regular_BoundedGlue_proof_d6b5ddec5d81
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:41:42.687481+00:00
-- url     : https://prove2.me/theorems/6b065f73-8176-4da2-a126-b24533c13b1f
-- title:
--   P2 M Ground Theory Heights  Heights Regular Bounded Glue proof d6b5ddec5d81: P2 M Ground Theory Heights  Heights Regular Bounded Glue proof d6b5ddec5d81
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Bounded Glue proof d6b5ddec5d81 construction uses the P2 M Ground Theory Heights  Heights Regular Bounded Glue proof d6b5ddec5d81 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PBoundedGlue.lean#L109-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PBoundedGlue.lean#L109-L215

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_RegMaxReindex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_BoundedStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PBoundedGlue
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
import Theorems.Thm_ReciprocityTheory_AnForm_levi_comp
import Theorems.Thm_ReciprocityTheory_AnForm_levi_congr
import Theorems.Thm_ReciprocityTheory_AnForm_levi_re_analytic

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
open Metric Filter Topology Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli regMax shrink)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_add_smul levi_re_analytic)
noncomputable section
open Classical

theorem P2M_GroundTheory_Heights__Heights_Regular_BoundedGlue_proof_d6b5ddec5d81 : BoundedGlue.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«BoundedGlue».«proof» := P2M_GroundTheory_Heights__Heights_Regular_BoundedGlue_proof_d6b5ddec5d81
