-- Prove2me | Theorems.Thm_P2M_DeciSigma1_Holes_Periodic_getElem__eq_of_root_eq_400ed337ec00
-- name    : P2M_DeciSigma1_Holes_Periodic_getElem__eq_of_root_eq_400ed337ec00
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:46:43.227811+00:00
-- url     : https://prove2.me/theorems/eb1165f4-7a7a-4e12-b9c0-59dd35a5d28a
-- title:
--   P2 M Deci Sigma1 Holes Periodic get Elem  eq of root eq 400ed337ec00: P2 M Deci Sigma1 Holes Periodic get Elem  eq of root eq 400ed337ec00
-- statement:
--   Pieces with equal roots agree on their first `d` letters, as `piece_suffixComparison` requires
--   at offsets `0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L290-L296
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L290-L296

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α : Type} {k : ℕ}
variable [DecidableEq α] {W : Fin k → List α} {d : ℕ}
omit [DecidableEq α]

theorem P2M_DeciSigma1_Holes_Periodic_getElem__eq_of_root_eq_400ed337ec00 (P Q : Piece W d) (h : P.root = Q.root) :
    ∀ t < d, t < P.len - 0 → (W P.coordinate)[P.start + 0 + t]? =
        (W Q.coordinate)[Q.start + 0 + t]? := by sorry

alias «DeciSigma1».«Holes».«Periodic».«getElem?_eq_of_root_eq» := P2M_DeciSigma1_Holes_Periodic_getElem__eq_of_root_eq_400ed337ec00
