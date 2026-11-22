-- Prove2me | Theorems.Thm_P2M_DeciSigma1_Holes_Periodic_Piece_getElem__eq_of_mod_eddd45ef4561
-- name    : P2M_DeciSigma1_Holes_Periodic_Piece_getElem__eq_of_mod_eddd45ef4561
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:47.632187+00:00
-- url     : https://prove2.me/theorems/abfd352b-617f-4e78-bb84-7b251d089855
-- title:
--   P2 M Deci Sigma1 Holes Periodic Piece get Elem  eq of mod eddd45ef4561: P2 M Deci Sigma1 Holes Periodic Piece get Elem  eq of mod eddd45ef4561
-- statement:
--   Letters of a piece at offsets congruent modulo `d` agree.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L106-L110
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L106-L110

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Order.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α : Type} {k : ℕ}
open DeciSigma1.Holes.Periodic.Piece
variable {W : Fin k → List α} {d : ℕ}

theorem P2M_DeciSigma1_Holes_Periodic_Piece_getElem__eq_of_mod_eddd45ef4561 (P : Piece W d) {o₁ o₂ : ℕ} (h₁ : o₁ < P.len) (h₂ : o₂ < P.len)
    (h : o₁ % d = o₂ % d) : (W P.coordinate)[P.start + o₁]? = (W P.coordinate)[P.start + o₂]? := by sorry

alias «DeciSigma1».«Holes».«Periodic».«Piece».«getElem?_eq_of_mod» := P2M_DeciSigma1_Holes_Periodic_Piece_getElem__eq_of_mod_eddd45ef4561
