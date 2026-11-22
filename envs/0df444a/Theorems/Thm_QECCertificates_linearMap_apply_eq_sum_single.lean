-- Prove2me | Theorems.Thm_QECCertificates_linearMap_apply_eq_sum_single
-- name    : QECCertificates.linearMap_apply_eq_sum_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:54:55.597805+00:00
-- url     : https://prove2.me/theorems/2c04deb9-c324-4ef2-a12b-59fb16b65e81
-- title:
--   QECCertificates: linear Map apply eq sum single
-- statement:
--   The matrix representation of a linear map in the standard basis:
--   `L x = Σ_i x_i · L(e_i)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KunnethCore.lean#L148-L154
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KunnethCore.lean#L148-L154

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_KunnethCore
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {p q r s a b : ℕ}

theorem QECCertificates.linearMap_apply_eq_sum_single (L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2)) (x : Vec p) :
    L x = fun k => ∑ i, x i * L (Pi.single i (1 : ZMod 2)) k := by sorry
