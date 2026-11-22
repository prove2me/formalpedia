-- Prove2me | Theorems.Thm_P2M_DeciSigma1_Words_getElem__deletePositions_1824c702cd1d
-- name    : P2M_DeciSigma1_Words_getElem__deletePositions_1824c702cd1d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:52.487821+00:00
-- url     : https://prove2.me/theorems/80827da1-e95f-4579-8199-85a3198edb88
-- title:
--   P2 M Deci Sigma1 Words get Elem  delete Positions 1824c702cd1d: P2 M Deci Sigma1 Words get Elem  delete Positions 1824c702cd1d
-- statement:
--   A retained letter of `w` is the letter of the edited word at the image of its position.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L205-L216
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L205-L216

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}

theorem P2M_DeciSigma1_Words_getElem__deletePositions_1824c702cd1d (w : List α) {a : ℕ} (hD : a ∉ D) (ha : a < w.length) :
    (deletePositions w D)[retainedCount D a]? = w[a]? := by sorry

alias «DeciSigma1».«Words».«getElem?_deletePositions» := P2M_DeciSigma1_Words_getElem__deletePositions_1824c702cd1d
