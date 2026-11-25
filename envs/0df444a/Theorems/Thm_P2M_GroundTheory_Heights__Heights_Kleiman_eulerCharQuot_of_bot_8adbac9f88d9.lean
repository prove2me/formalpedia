-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_eulerCharQuot_of_bot_8adbac9f88d9
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_eulerCharQuot_of_bot_8adbac9f88d9
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:00:44.794062+00:00
-- url     : https://prove2.me/theorems/e24d5f21-c8a5-41d1-b952-41fba9685b16
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman euler Char Quot of bot 8adbac9f88d9: P2 M Ground Theory Heights  Heights Kleiman euler Char Quot of bot 8adbac9f88d9
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman euler Char Quot of bot 8adbac9f88d9 construction uses the P2 M Ground Theory Heights  Heights Kleiman euler Char Quot of bot 8adbac9f88d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperDevissage.lean#L123-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperDevissage.lean#L123-L136

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_eulerCharQuot_of_bot_8adbac9f88d9 (F₁ F₂ : SubSystem k x E) (h : ∀ I, F₂.sub I = ⊥) :
    eulerCharQuot k F₁ F₂ = eulerChar k F₁ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«eulerCharQuot_of_bot» := P2M_GroundTheory_Heights__Heights_Kleiman_eulerCharQuot_of_bot_8adbac9f88d9
