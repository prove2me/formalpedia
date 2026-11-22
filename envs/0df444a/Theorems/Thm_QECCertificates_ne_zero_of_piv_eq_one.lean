-- Prove2me | Theorems.Thm_QECCertificates_ne_zero_of_piv_eq_one
-- name    : QECCertificates.ne_zero_of_piv_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:53:50.770057+00:00
-- url     : https://prove2.me/theorems/58b75e4c-f860-4b72-8e2d-5bf3c8e5e403
-- title:
--   QECCertificates: ne zero of piv eq one
-- statement:
--   A row that takes the value 1 on its pivot column is non-zero.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Canonical.lean#L142-L143
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Canonical.lean#L142-L143

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.ne_zero_of_piv_eq_one {v : Vec n} {p : Fin n} (h : v p = 1) : v ≠ 0 := by sorry
