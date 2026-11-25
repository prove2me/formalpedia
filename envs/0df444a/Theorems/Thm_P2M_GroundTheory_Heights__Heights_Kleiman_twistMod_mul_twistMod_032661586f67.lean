-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistMod_mul_twistMod_032661586f67
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twistMod_mul_twistMod_032661586f67
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:21:10.048814+00:00
-- url     : https://prove2.me/theorems/50e56e99-b21f-4884-b537-9d0302658989
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman twist Mod mul twist Mod 032661586f67: P2 M Ground Theory Heights  Heights Kleiman twist Mod mul twist Mod 032661586f67
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman twist Mod mul twist Mod 032661586f67 construction uses the P2 M Ground Theory Heights  Heights Kleiman twist Mod mul twist Mod 032661586f67 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L36-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L36-L41

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twistMod_mul_twistMod_032661586f67 (a b : ℤ) (I : Chart x) :
    twistMod k x a I * twistMod k x b I = twistMod k x (a + b) I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twistMod_mul_twistMod» := P2M_GroundTheory_Heights__Heights_Kleiman_twistMod_mul_twistMod_032661586f67
