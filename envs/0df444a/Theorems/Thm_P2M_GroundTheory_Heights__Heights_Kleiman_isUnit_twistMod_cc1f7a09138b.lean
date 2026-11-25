-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isUnit_twistMod_cc1f7a09138b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_isUnit_twistMod_cc1f7a09138b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:04:31.60449+00:00
-- url     : https://prove2.me/theorems/40dbe3ab-4c02-504a-9035-dae159aa19ea
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman is Unit twist Mod cc1f7a09138b: P2 M Ground Theory Heights  Heights Kleiman is Unit twist Mod cc1f7a09138b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman is Unit twist Mod cc1f7a09138b construction uses the P2 M Ground Theory Heights  Heights Kleiman is Unit twist Mod cc1f7a09138b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L88-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L88-L90

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_isUnit_twistMod_cc1f7a09138b (c : ℤ) (I : Chart x) : IsUnit (twistMod k x c I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«isUnit_twistMod» := P2M_GroundTheory_Heights__Heights_Kleiman_isUnit_twistMod_cc1f7a09138b
