-- Prove2me | Theorems.Thm_QECCertificates_eq_zero_of_lt_leadIdx
-- name    : QECCertificates.eq_zero_of_lt_leadIdx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:53:49.395463+00:00
-- url     : https://prove2.me/theorems/81d0166e-b2b4-45a9-8141-57ca9b97106a
-- title:
--   QECCertificates: eq zero of lt lead Idx
-- statement:
--   Everything before `leadIdx` is zero.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Canonical.lean#L150-L153
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Canonical.lean#L150-L153

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.eq_zero_of_lt_leadIdx {v : Vec n} (h : v ≠ 0) {i : Fin n} (hi : i < leadIdx v h) :
    v i = 0 := by sorry
