-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isVeryAmple_twistSys_one_40d8ce118432
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_isVeryAmple_twistSys_one_40d8ce118432
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:09:10.140752+00:00
-- url     : https://prove2.me/theorems/ae28d9ee-4bb5-4aef-97d4-b99170bb8218
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman is Very Ample twist Sys one 40d8ce118432: P2 M Ground Theory Heights  Heights Kleiman is Very Ample twist Sys one 40d8ce118432
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman is Very Ample twist Sys one 40d8ce118432 construction uses the P2 M Ground Theory Heights  Heights Kleiman is Very Ample twist Sys one 40d8ce118432 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/AlgebraMapMemChartRingLine.lean#L348-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/AlgebraMapMemChartRingLine.lean#L348-L348

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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_isVeryAmple_twistSys_one_40d8ce118432 : IsVeryAmple (twistSys S x 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«isVeryAmple_twistSys_one» := P2M_GroundTheory_Heights__Heights_Kleiman_isVeryAmple_twistSys_one_40d8ce118432
