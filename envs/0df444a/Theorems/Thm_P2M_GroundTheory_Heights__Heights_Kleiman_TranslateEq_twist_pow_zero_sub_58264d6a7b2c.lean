-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_twist_pow_zero_sub_58264d6a7b2c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_twist_pow_zero_sub_58264d6a7b2c
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:29:02.016524+00:00
-- url     : https://prove2.me/theorems/09eced99-bfbe-42c4-988a-6936176fba40
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Translate Eq twist pow zero sub 58264d6a7b2c: P2 M Ground Theory Heights  Heights Kleiman Translate Eq twist pow zero sub 58264d6a7b2c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Translate Eq twist pow zero sub 58264d6a7b2c construction uses the P2 M Ground Theory Heights  Heights Kleiman Translate Eq twist pow zero sub 58264d6a7b2c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistPowZeroSub.lean#L19-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistPowZeroSub.lean#L19-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NotTwistFiniteAtZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisAltAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistPowZeroSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_twist_pow_zero_sub_58264d6a7b2c (G B : Kleiman.SubSystem S x Ω) (I : Kleiman.Chart x) :
    ((G.twist (B.pow 0)).sub I).restrictScalars S = (G.sub I).restrictScalars S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TranslateEq».«twist_pow_zero_sub» := P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_twist_pow_zero_sub_58264d6a7b2c
