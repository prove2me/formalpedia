-- Prove2me | Theorems.Thm_ReaderSel_left_unit
-- name    : ReaderSel.left_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:31:42.782173+00:00
-- url     : https://prove2.me/theorems/9913c7ba-e6b8-42d6-b2fb-f6f1a3078556
-- title:
--   Reader Sel: left unit
-- statement:
--   Left unit: bind (pure f) g a = (g (f a)).eval a
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ReaderMonad.lean#L49-L52
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ReaderMonad.lean#L49-L52

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ReaderMonad
set_option autoImplicit true
@[expose] public section
public section
universe u v w

theorem ReaderSel.left_unit {ι : Type u} {α : Type v} {γ : Type w}
    (i₀ : ι) (f : α → γ)
    (g : γ → ReaderSel ι α γ) (a : α) :
    (ReaderSel.pure i₀ f |>.bind g).eval a = (g (f a)).eval a := by sorry
