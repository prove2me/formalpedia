-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistPows_sub_eq_bot_405b85e0afc3
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twistPows_sub_eq_bot_405b85e0afc3
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:03:53.08553+00:00
-- url     : https://prove2.me/theorems/79a584b4-53b1-44bf-8678-7f607cc4dd8c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman twist Pows sub eq bot 405b85e0afc3: P2 M Ground Theory Heights  Heights Kleiman twist Pows sub eq bot 405b85e0afc3
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman twist Pows sub eq bot 405b85e0afc3 construction uses the P2 M Ground Theory Heights  Heights Kleiman twist Pows sub eq bot 405b85e0afc3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperDevissage.lean#L103-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperDevissage.lean#L103-L106

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twistPows_sub_eq_bot_405b85e0afc3 {F : SubSystem k x E} (hF : ∀ I, F.sub I = ⊥) :
    ∀ (t : ℕ) (L : Fin t → SubSystem k x Ω) (n : Fin t → ℕ) (I : Chart x), (F.twistPows t L n).sub I = ⊥
  := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twistPows_sub_eq_bot» := P2M_GroundTheory_Heights__Heights_Kleiman_twistPows_sub_eq_bot_405b85e0afc3
