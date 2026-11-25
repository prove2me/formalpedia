-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_le_range_5e99bf35a03e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_le_range_5e99bf35a03e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:03:30.84178+00:00
-- url     : https://prove2.me/theorems/34b810ff-af68-448c-aaa9-da807620e81c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman ideal Mod le range 5e99bf35a03e: P2 M Ground Theory Heights  Heights Kleiman ideal Mod le range 5e99bf35a03e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman ideal Mod le range 5e99bf35a03e construction uses the P2 M Ground Theory Heights  Heights Kleiman ideal Mod le range 5e99bf35a03e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThree.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThree.lean#L21-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnW
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThree
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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_le_range_5e99bf35a03e (J : Ideal (Poly k N)) (I : Chart x) :
    idealMod (x := x) J I ≤ LinearMap.range (Algebra.linearMap (chartRing k x I) Ω) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«idealMod_le_range» := P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_le_range_5e99bf35a03e
