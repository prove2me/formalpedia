-- Prove2me | Theorems.Thm_P2M_DeciSigma1_Holes_Periodic_AdmissibleDeletion_getElem__imagePiece_5b6104921581
-- name    : P2M_DeciSigma1_Holes_Periodic_AdmissibleDeletion_getElem__imagePiece_5b6104921581
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:43:19.385502+00:00
-- url     : https://prove2.me/theorems/e16c664a-dc34-485d-af9b-daefba9c8dd0
-- title:
--   P2 M Deci Sigma1 Holes Periodic Admissible Deletion get Elem  image Piece 5b6104921581: P2 M Deci Sigma1 Holes Periodic Admissible Deletion get Elem  image Piece 5b6104921581
-- statement:
--   The P2 M Deci Sigma1 Holes Periodic Admissible Deletion get Elem  image Piece 5b6104921581 construction uses the P2 M Deci Sigma1 Holes Periodic Admissible Deletion get Elem  image Piece 5b6104921581 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L383-L386
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L383-L386

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α S : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α} {ρ : List α}
open DeciSigma1.Holes.Periodic.AdmissibleDeletion
variable {N : ℕ} {x : Piece W ρ.length → ℕ} (hx : AdmissibleDeletion W ρ N x)
include hx

theorem P2M_DeciSigma1_Holes_Periodic_AdmissibleDeletion_getElem__imagePiece_5b6104921581 (P : Piece W ρ.length) {o : ℕ}
    (ho : o < retainedLength (N := N) (x := x) P) :
    (editedTuple W ρ N x P.coordinate)[(hx.imagePiece P).start + o]? =
        (W P.coordinate)[P.start + o]? := by sorry

alias «DeciSigma1».«Holes».«Periodic».«AdmissibleDeletion».«getElem?_imagePiece» := P2M_DeciSigma1_Holes_Periodic_AdmissibleDeletion_getElem__imagePiece_5b6104921581
