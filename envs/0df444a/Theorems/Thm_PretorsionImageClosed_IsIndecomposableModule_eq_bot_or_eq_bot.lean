-- Prove2me | Theorems.Thm_PretorsionImageClosed_IsIndecomposableModule_eq_bot_or_eq_bot
-- name    : PretorsionImageClosed.IsIndecomposableModule.eq_bot_or_eq_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:08:27.418318+00:00
-- url     : https://prove2.me/theorems/da71752b-fea0-441f-8586-724f47b7b69f
-- title:
--   Is Indecomposable Module: eq bot or eq bot
-- statement:
--   The Is Indecomposable Module construction uses the eq bot or eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/IndecomposableModule.lean#L67-L70
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/IndecomposableModule.lean#L67-L70

module
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Definitions.Def_PretorsionImageClosed_Modules_LocalRingIdempotents
public import Definitions.Def_PretorsionImageClosed_Modules_IndecomposableModule
set_option autoImplicit true
@[expose] public section
public section
open PretorsionImageClosed
universe u v w
variable (A : Type u) (M : Type v) [Semiring A] [AddCommMonoid M] [Module A M]
variable {A M}

theorem PretorsionImageClosed.IsIndecomposableModule.eq_bot_or_eq_bot
    (h : IsIndecomposableModule A M) {N P : Submodule A M}
    (hNP : IsCompl N P) : N = ⊥ ∨ P = ⊥ := by sorry
