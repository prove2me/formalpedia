-- Prove2me | Theorems.Thm_P2M_GlobalTheory_isoTransvection_form_apply_apply__4bb9787d073f
-- name    : P2M_GlobalTheory_isoTransvection_form_apply_apply__4bb9787d073f
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:11:58.178168+00:00
-- url     : https://prove2.me/theorems/2adfdd64-a3ba-4b4a-9a49-463a7b846313
-- title:
--   P2 M Global Theory iso Transvection form apply apply  4bb9787d073f: P2 M Global Theory iso Transvection form apply apply  4bb9787d073f
-- statement:
--   The P2 M Global Theory iso Transvection form apply apply  4bb9787d073f construction uses the P2 M Global Theory iso Transvection form apply apply  4bb9787d073f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L108-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L108-L112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module
variable {R M : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]
open GlobalTheory.isoTransvection
variable (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0)
variable {h}

theorem P2M_GlobalTheory_isoTransvection_form_apply_apply__4bb9787d073f (hh : ∀ u v, h v u = star (h u v)) (b b' : R) (u v : M) :
    h (isoTransvection h x hx b u) (isoTransvection h x hx b' v)
      = h u v + (b + star b') * h u x * h x v := by sorry

alias «GlobalTheory».«isoTransvection».«form_apply_apply'» := P2M_GlobalTheory_isoTransvection_form_apply_apply__4bb9787d073f
