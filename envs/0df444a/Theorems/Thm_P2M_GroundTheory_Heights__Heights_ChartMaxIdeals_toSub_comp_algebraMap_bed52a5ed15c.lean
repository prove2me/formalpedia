-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_toSub_comp_algebraMap_bed52a5ed15c
-- name    : P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_toSub_comp_algebraMap_bed52a5ed15c
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:16:37.513716+00:00
-- url     : https://prove2.me/theorems/9893739f-da91-482d-a838-bcd47548e5bb
-- title:
--   P2 M Ground Theory Heights  Heights Chart Max Ideals to Sub comp algebra Map bed52a5ed15c: P2 M Ground Theory Heights  Heights Chart Max Ideals to Sub comp algebra Map bed52a5ed15c
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Max Ideals to Sub comp algebra Map bed52a5ed15c construction uses the P2 M Ground Theory Heights  Heights Chart Max Ideals to Sub comp algebra Map bed52a5ed15c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartMaxIdeals.lean#L64-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartMaxIdeals.lean#L64-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProperSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartMaxIdeals
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMaxIdeals
variable {F : Type} [Field F] {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_toSub_comp_algebraMap_bed52a5ed15c {I W : Ideal (MvPolynomial (Fin n) F)} (h : I ≤ W) (t : Fin n → F) :
    (toSub h t e).comp (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) =
      algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc W t e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMaxIdeals».«toSub_comp_algebraMap» := P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_toSub_comp_algebraMap_bed52a5ed15c
