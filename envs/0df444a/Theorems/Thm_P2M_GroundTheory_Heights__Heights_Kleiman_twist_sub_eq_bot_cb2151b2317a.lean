-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twist_sub_eq_bot_cb2151b2317a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twist_sub_eq_bot_cb2151b2317a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:11:24.873273+00:00
-- url     : https://prove2.me/theorems/8239cfbf-fa3b-5941-b547-82832ca44ccc
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman twist sub eq bot cb2151b2317a: P2 M Ground Theory Heights  Heights Kleiman twist sub eq bot cb2151b2317a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman twist sub eq bot cb2151b2317a construction uses the P2 M Ground Theory Heights  Heights Kleiman twist sub eq bot cb2151b2317a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperDevissage.lean#L94-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperDevissage.lean#L94-L99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDevissage
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
universe u v w u₁ v₁ w₁
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
omit [Module k E] [IsScalarTower k Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twist_sub_eq_bot_cb2151b2317a {F : SubSystem k x E} (hF : ∀ I, F.sub I = ⊥) (Q : SubSystem k x Ω) (I : Chart x) :
    (F.twist Q).sub I = ⊥ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twist_sub_eq_bot» := P2M_GroundTheory_Heights__Heights_Kleiman_twist_sub_eq_bot_cb2151b2317a
