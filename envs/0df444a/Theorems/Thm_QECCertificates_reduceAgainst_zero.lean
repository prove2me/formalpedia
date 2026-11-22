-- Prove2me | Theorems.Thm_QECCertificates_reduceAgainst_zero
-- name    : QECCertificates.reduceAgainst_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:56:20.563342+00:00
-- url     : https://prove2.me/theorems/6249b224-996a-4a81-89bf-426c1c8d3c2d
-- title:
--   QECCertificates: reduce Against zero
-- statement:
--   The reduction maps zero to zero.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Membership.lean#L57-L62
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Membership.lean#L57-L62

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Membership
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.reduceAgainst_zero (D : List (PivRow n)) : reduceAgainst D (0 : Vec n) = 0 := by sorry
