-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_ofSecond_mods_63f974983985
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_ofSecond_mods_63f974983985
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:01:25.643084+00:00
-- url     : https://prove2.me/theorems/3003fe0f-ab21-4b91-a402-1252b025c2dd
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Translate Eq of Second mods 63f974983985: P2 M Ground Theory Heights  Heights Kleiman Translate Eq of Second mods 63f974983985
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Translate Eq of Second mods 63f974983985 construction uses the P2 M Ground Theory Heights  Heights Kleiman Translate Eq of Second mods 63f974983985 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwinEqBundle.lean#L330-L343
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwinEqBundle.lean#L330-L343

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisAltAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqBundleLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqBundle
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
noncomputable section
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
variable (Q' : IndefiniteRowSideFullHecke.Kleiman.LineBundle (S := S) x)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_ofSecond_mods_63f974983985 {i : Fin (N + 1)} (h : x i ≠ 0) : Q'.mods i = toIndefiniteRowSideFullHecke (ofSecond Q').toSubSystem i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TranslateEq».«ofSecond_mods» := P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_ofSecond_mods_63f974983985
