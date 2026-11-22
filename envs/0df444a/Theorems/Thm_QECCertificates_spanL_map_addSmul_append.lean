-- Prove2me | Theorems.Thm_QECCertificates_spanL_map_addSmul_append
-- name    : QECCertificates.spanL_map_addSmul_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:49.690714+00:00
-- url     : https://prove2.me/theorems/953c3db1-2a18-4703-8bbb-877e75e585d0
-- title:
--   QECCertificates: span L map add Smul append
-- statement:
--   **Preservation of the row space (whole-list version)**: replacing every row `r` of a
--   list `A` by `r + f r • w` and then appending `w` at the end gives the same row space as
--   appending `w` to `A`.
--
--   This is the correctness skeleton of row reduction: elimination performs only the one
--   operation of adding the new row to an old row with a coefficient, which does not change
--   the spanned subspace and hence does not change the code.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L240-L264
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L240-L264

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.spanL_map_addSmul_append (A : List (Vec n)) (w : Vec n) (f : Vec n → ZMod 2) :
    spanL (A.map (fun r => r + f r • w) ++ [w]) = spanL (A ++ [w]) := by sorry
