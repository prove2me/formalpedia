-- Prove2me | Theorems.Thm_QECCertificates_dotProduct_e_sum
-- name    : QECCertificates.dotProduct_e_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:51.681679+00:00
-- url     : https://prove2.me/theorems/50f7f3d2-b5db-4309-9c89-dfefc1c03d24
-- title:
--   QECCertificates: dot Product e sum
-- statement:
--   **Dot-product reduction**: pairing a sum of basis vectors with `v` reads the components
--   of `v` on that support, so a check-row comparison costs `|A|` terms, not `n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basis.lean#L55-L61
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basis.lean#L55-L61

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basis
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.dotProduct_e_sum (A : List (Fin n)) (v : Vec n) :
    ((A.map e).sum) ⬝ᵥ v = (A.map v).sum := by sorry
