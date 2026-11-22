-- Prove2me | Theorems.Thm_P2M_DeciSigma1_Words_getElem__deletePositions_eq_f9d47ab0e923
-- name    : P2M_DeciSigma1_Words_getElem__deletePositions_eq_f9d47ab0e923
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:20.969807+00:00
-- url     : https://prove2.me/theorems/01e211e9-8f3e-41f9-9e60-55088cc33157
-- title:
--   P2 M Deci Sigma1 Words get Elem  delete Positions eq f9d47ab0e923: P2 M Deci Sigma1 Words get Elem  delete Positions eq f9d47ab0e923
-- statement:
--   The letter of the edited word at a cut is the letter of the original word at the greatest
--   preimage of the cut.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L276-L282
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L276-L282

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

theorem P2M_DeciSigma1_Words_getElem__deletePositions_eq_f9d47ab0e923 (w : List α) (a : ℕ) :
    (deletePositions w D)[a]? = w[greatestPreimage D a]? := by sorry

alias «DeciSigma1».«Words».«getElem?_deletePositions_eq» := P2M_DeciSigma1_Words_getElem__deletePositions_eq_f9d47ab0e923
