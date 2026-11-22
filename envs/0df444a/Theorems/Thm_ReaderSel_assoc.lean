-- Prove2me | Theorems.Thm_ReaderSel_assoc
-- name    : ReaderSel.assoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:31:45.517234+00:00
-- url     : https://prove2.me/theorems/d244447f-2466-4061-97bb-b501835f923e
-- title:
--   Reader Sel: assoc
-- statement:
--   Associativity: bind (bind r f) g = bind r (fun v => bind (f v) g)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ReaderMonad.lean#L60-L63
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ReaderMonad.lean#L60-L63

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ReaderMonad
set_option autoImplicit true
@[expose] public section
public section
universe u v w

theorem ReaderSel.assoc {ι : Type u} {α : Type v} {γ : Type w}
    (r : ReaderSel ι α γ)
    (f : γ → ReaderSel ι α γ) (g : γ → ReaderSel ι α γ) (a : α) :
    ((r.bind f).bind g).eval a = (r.bind (fun v => (f v).bind g)).eval a := by sorry
