-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartChoice_specFirst_rename_shiftVar_52c27ad67f52
-- name    : P2M_GroundTheory_Heights__Heights_ChartChoice_specFirst_rename_shiftVar_52c27ad67f52
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:17:11.822055+00:00
-- url     : https://prove2.me/theorems/3cb29618-3bc2-44f8-90c8-ef519cbb73b0
-- title:
--   P2 M Ground Theory Heights  Heights Chart Choice spec First rename shift Var 52c27ad67f52: P2 M Ground Theory Heights  Heights Chart Choice spec First rename shift Var 52c27ad67f52
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Choice spec First rename shift Var 52c27ad67f52 construction uses the P2 M Ground Theory Heights  Heights Chart Choice spec First rename shift Var 52c27ad67f52 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartChoice.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartChoice.lean#L41-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartChoice
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
open GroundTheory.Heights₂.Heights.ChartChoice
variable {F : Type} [Field F] {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartChoice_specFirst_rename_shiftVar_52c27ad67f52 (q : MvPolynomial (Fin e × Fin n) F) :
    specFirst (rename (shiftVar e n) q) 0 = q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartChoice».«specFirst_rename_shiftVar» := P2M_GroundTheory_Heights__Heights_ChartChoice_specFirst_rename_shiftVar_52c27ad67f52
