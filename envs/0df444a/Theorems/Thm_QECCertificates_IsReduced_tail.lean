-- Prove2me | Theorems.Thm_QECCertificates_IsReduced_tail
-- name    : QECCertificates.IsReduced.tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:45:42.746483+00:00
-- url     : https://prove2.me/theorems/78756341-aac3-4e6f-b6c0-7f8b4f986d13
-- title:
--   Is Reduced: tail
-- statement:
--   The tail of a mutually reduced list is again mutually reduced.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L105-L109
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L105-L109

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

theorem QECCertificates.IsReduced.tail {r : PivRow n} {D : List (PivRow n)} (h : IsReduced (r :: D)) :
    IsReduced D := by sorry
