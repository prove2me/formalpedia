-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isVeryAmpleBy_twistSys_one_0b95c573b325
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_isVeryAmpleBy_twistSys_one_0b95c573b325
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:04:24.315858+00:00
-- url     : https://prove2.me/theorems/e66fac3b-2048-5473-8511-b8bd083299d1
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman is Very Ample By twist Sys one 0b95c573b325: P2 M Ground Theory Heights  Heights Kleiman is Very Ample By twist Sys one 0b95c573b325
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman is Very Ample By twist Sys one 0b95c573b325 construction uses the P2 M Ground Theory Heights  Heights Kleiman is Very Ample By twist Sys one 0b95c573b325 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/AlgebraMapMemChartRingLine.lean#L334-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/AlgebraMapMemChartRingLine.lean#L334-L346

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_isVeryAmpleBy_twistSys_one_0b95c573b325 : IsVeryAmpleBy (twistSys S x 1) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«isVeryAmpleBy_twistSys_one» := P2M_GroundTheory_Heights__Heights_Kleiman_isVeryAmpleBy_twistSys_one_0b95c573b325
