-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistMod_pow_eq_13112438b8ce
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twistMod_pow_eq_13112438b8ce
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:06:35.369826+00:00
-- url     : https://prove2.me/theorems/8ec37d88-cf1f-5d60-8a57-fc29ab7d4ba1
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman twist Mod pow eq 13112438b8ce: P2 M Ground Theory Heights  Heights Kleiman twist Mod pow eq 13112438b8ce
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman twist Mod pow eq 13112438b8ce construction uses the P2 M Ground Theory Heights  Heights Kleiman twist Mod pow eq 13112438b8ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L43-L47

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twistMod_pow_eq_13112438b8ce (c : ℤ) (n : ℕ) (I : Chart x) :
    twistMod k x c I ^ n = twistMod k x (n * c) I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twistMod_pow_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_twistMod_pow_eq_13112438b8ce
