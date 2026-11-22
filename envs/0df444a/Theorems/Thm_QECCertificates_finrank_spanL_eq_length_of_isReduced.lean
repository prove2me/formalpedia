-- Prove2me | Theorems.Thm_QECCertificates_finrank_spanL_eq_length_of_isReduced
-- name    : QECCertificates.finrank_spanL_eq_length_of_isReduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:53:29.898115+00:00
-- url     : https://prove2.me/theorems/c6ca39dc-f791-4537-aa2e-f028b357fbf7
-- title:
--   QECCertificates: finrank span L eq length of is Reduced
-- statement:
--   **The rank equals the number of rows of the reduction output** (stated for an already
--   reduced state).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L186-L193
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L186-L193

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

theorem QECCertificates.finrank_spanL_eq_length_of_isReduced {D : List (PivRow n)} (hD : IsReduced D)
    (hnd : NodupPiv D) :
    Module.finrank (ZMod 2) (spanL (rowList D)) = D.length := by sorry
