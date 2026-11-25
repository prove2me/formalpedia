-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twist_idealSys_primeOf_sub_9fa796ef3d4e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twist_idealSys_primeOf_sub_9fa796ef3d4e
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:03:57.337544+00:00
-- url     : https://prove2.me/theorems/1ca31758-99b2-4e75-baad-97a308754c6d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman twist ideal Sys prime Of sub 9fa796ef3d4e: P2 M Ground Theory Heights  Heights Kleiman twist ideal Sys prime Of sub 9fa796ef3d4e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman twist ideal Sys prime Of sub 9fa796ef3d4e construction uses the P2 M Ground Theory Heights  Heights Kleiman twist ideal Sys prime Of sub 9fa796ef3d4e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperDevissage.lean#L110-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperDevissage.lean#L110-L121

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twist_idealSys_primeOf_sub_9fa796ef3d4e (F : SubSystem k x E) (I : Chart x) :
    (F.twist (idealSys x (primeOf (S := k) x))).sub I = ⊥ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twist_idealSys_primeOf_sub» := P2M_GroundTheory_Heights__Heights_Kleiman_twist_idealSys_primeOf_sub_9fa796ef3d4e
