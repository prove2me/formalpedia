-- Prove2me | Theorems.Thm_QECCertificates_range_get_eq_rowList
-- name    : QECCertificates.range_get_eq_rowList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:45:47.343345+00:00
-- url     : https://prove2.me/theorems/07bf6249-059d-48f0-901b-df5e266416fb
-- title:
--   QECCertificates: range get eq row List
-- statement:
--   The range of `D.get` is exactly the list of rows of `D`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L161-L174
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L161-L174

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
open _root_.Matrix
variable {n : ℕ}

theorem QECCertificates.range_get_eq_rowList (D : List (PivRow n)) :
    Set.range (fun i : Fin D.length => (D.get i).1) = {x | x ∈ rowList D} := by sorry
