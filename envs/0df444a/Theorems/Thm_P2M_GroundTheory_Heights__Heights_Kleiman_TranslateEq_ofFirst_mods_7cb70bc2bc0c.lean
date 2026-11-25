-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_ofFirst_mods_7cb70bc2bc0c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_ofFirst_mods_7cb70bc2bc0c
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:00:17.157276+00:00
-- url     : https://prove2.me/theorems/db53b873-cb8f-41e7-a309-113f80aa1b91
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Translate Eq of First mods 7cb70bc2bc0c: P2 M Ground Theory Heights  Heights Kleiman Translate Eq of First mods 7cb70bc2bc0c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Translate Eq of First mods 7cb70bc2bc0c construction uses the P2 M Ground Theory Heights  Heights Kleiman Translate Eq of First mods 7cb70bc2bc0c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwinEqBundle.lean#L184-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwinEqBundle.lean#L184-L185

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
variable (Q : Kleiman.LineBundle S x)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_ofFirst_mods_7cb70bc2bc0c (i : Fin (N + 1)) : (ofFirst Q).mods i = toIndefiniteRowSideFullHecke Q.toSubSystem i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TranslateEq».«ofFirst_mods» := P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_ofFirst_mods_7cb70bc2bc0c
