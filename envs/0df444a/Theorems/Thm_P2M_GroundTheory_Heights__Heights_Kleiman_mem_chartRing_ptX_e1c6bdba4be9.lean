-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_chartRing_ptX_e1c6bdba4be9
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_mem_chartRing_ptX_e1c6bdba4be9
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:15:17.20727+00:00
-- url     : https://prove2.me/theorems/36743e04-a2db-4416-b0c7-11f7a24bf48b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman mem chart Ring pt X e1c6bdba4be9: P2 M Ground Theory Heights  Heights Kleiman mem chart Ring pt X e1c6bdba4be9
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman mem chart Ring pt X e1c6bdba4be9 construction uses the P2 M Ground Theory Heights  Heights Kleiman mem chart Ring pt X e1c6bdba4be9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/AlgebraMapMemChartRingLine.lean#L436-L437
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/AlgebraMapMemChartRingLine.lean#L436-L437

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u v w
variable (k : Type u) [Field k]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_mem_chartRing_ptX_e1c6bdba4be9 (I : Chart (ptX k)) (a : k) : a ∈ chartRing k (ptX k) I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«mem_chartRing_ptX» := P2M_GroundTheory_Heights__Heights_Kleiman_mem_chartRing_ptX_e1c6bdba4be9
