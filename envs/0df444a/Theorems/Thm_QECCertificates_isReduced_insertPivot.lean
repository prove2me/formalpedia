-- Prove2me | Theorems.Thm_QECCertificates_isReduced_insertPivot
-- name    : QECCertificates.isReduced_insertPivot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:27.529861+00:00
-- url     : https://prove2.me/theorems/e8f7c14d-c3a0-45f4-96b6-428ad37c3a18
-- title:
--   QECCertificates: is Reduced insert Pivot
-- statement:
--   Insertion preserves the mutual-reduction invariant: it requires `w` to be 0 at every pivot
--       column of `D` and 1 at the new pivot column.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RowReduce.lean#L191-L224
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RowReduce.lean#L191-L224

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.isReduced_insertPivot {D : List (PivRow n)} (hD : IsReduced D) {w : Vec n} {p : Fin n}
    (hp : w p = 1) (hz : ∀ ri ∈ D, w ri.2 = 0) : IsReduced (insertPivot D w p) := by sorry
