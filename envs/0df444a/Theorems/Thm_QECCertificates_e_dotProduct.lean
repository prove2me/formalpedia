-- Prove2me | Theorems.Thm_QECCertificates_e_dotProduct
-- name    : QECCertificates.e_dotProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:47:57.758805+00:00
-- url     : https://prove2.me/theorems/693a92ac-7296-4184-9694-b0aff6930cbf
-- title:
--   QECCertificates: e dot Product
-- statement:
--   A basis vector pairs with `v` to the component of `v` at that position.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basis.lean#L47-L51
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basis.lean#L47-L51

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basis
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.e_dotProduct (a : Fin n) (v : Vec n) : e a ⬝ᵥ v = v a := by sorry
