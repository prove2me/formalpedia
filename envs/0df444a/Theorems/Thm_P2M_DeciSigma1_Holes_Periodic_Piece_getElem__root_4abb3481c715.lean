-- Prove2me | Theorems.Thm_P2M_DeciSigma1_Holes_Periodic_Piece_getElem__root_4abb3481c715
-- name    : P2M_DeciSigma1_Holes_Periodic_Piece_getElem__root_4abb3481c715
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:55.076819+00:00
-- url     : https://prove2.me/theorems/360836bc-0f42-4bb4-b713-103e3374eb66
-- title:
--   P2 M Deci Sigma1 Holes Periodic Piece get Elem  root 4abb3481c715: P2 M Deci Sigma1 Holes Periodic Piece get Elem  root 4abb3481c715
-- statement:
--   The P2 M Deci Sigma1 Holes Periodic Piece get Elem  root 4abb3481c715 construction uses the P2 M Deci Sigma1 Holes Periodic Piece get Elem  root 4abb3481c715 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L112-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L112-L118

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

theorem P2M_DeciSigma1_Holes_Periodic_Piece_getElem__root_4abb3481c715 (P : Piece W d) {o : ℕ} (h : o < P.len) :
    (W P.coordinate)[P.start + o]? = P.root[o % d]? := by sorry

alias «DeciSigma1».«Holes».«Periodic».«Piece».«getElem?_root» := P2M_DeciSigma1_Holes_Periodic_Piece_getElem__root_4abb3481c715
