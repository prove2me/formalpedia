-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_generated_twistSys_zero_69b6ba3803f8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_generated_twistSys_zero_69b6ba3803f8
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:59:59.494801+00:00
-- url     : https://prove2.me/theorems/403a3111-2a8f-4143-b82c-d3d7d0e2266b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman generated twist Sys zero 69b6ba3803f8: P2 M Ground Theory Heights  Heights Kleiman generated twist Sys zero 69b6ba3803f8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman generated twist Sys zero 69b6ba3803f8 construction uses the P2 M Ground Theory Heights  Heights Kleiman generated twist Sys zero 69b6ba3803f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L73-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L73-L80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
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
open MvPolynomial
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_generated_twistSys_zero_69b6ba3803f8 : (twistSys k x 0).Generated := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«generated_twistSys_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_generated_twistSys_zero_69b6ba3803f8
