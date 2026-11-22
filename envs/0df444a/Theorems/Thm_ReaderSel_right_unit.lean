-- Prove2me | Theorems.Thm_ReaderSel_right_unit
-- name    : ReaderSel.right_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:31:43.589285+00:00
-- url     : https://prove2.me/theorems/21e44c68-67af-42e3-8d44-513159c2dad9
-- title:
--   Reader Sel: right unit
-- statement:
--   Right unit: bind r (fun v => pure (const v)) a = r.eval a
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ReaderMonad.lean#L55-L57
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ReaderMonad.lean#L55-L57

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ReaderMonad
set_option autoImplicit true
@[expose] public section
public section
universe u v w

theorem ReaderSel.right_unit {ι : Type u} {α : Type v} {γ : Type w}
    (r : ReaderSel ι α γ) (i₀ : ι) (a : α) :
    (r.bind (fun v => ReaderSel.pure i₀ (fun _ => v))).eval a = r.eval a := by sorry
