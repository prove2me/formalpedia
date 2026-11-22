-- Prove2me | Theorems.Thm_QECCertificates_dotProduct_e
-- name    : QECCertificates.dotProduct_e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:02:20.020495+00:00
-- url     : https://prove2.me/theorems/e3bc0b2a-05ac-49dc-af56-46279fb98c96
-- title:
--   QECCertificates: dot Product e
-- statement:
--   The commuted form: a basis vector on the **right** of a pairing. Two call sites want this
--   shape rather than the one above, and stating it once keeps them from rediscovering it.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basis.lean#L94-L95
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basis.lean#L94-L95

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basis
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.dotProduct_e (v : Vec n) (a : Fin n) : v ⬝ᵥ e a = v a := by sorry
