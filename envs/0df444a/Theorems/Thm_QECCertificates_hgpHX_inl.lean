-- Prove2me | Theorems.Thm_QECCertificates_hgpHX_inl
-- name    : QECCertificates.hgpHX_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:47:59.60971+00:00
-- url     : https://prove2.me/theorems/70d7d6d6-e2e3-479f-883a-103ac0b33169
-- title:
--   QECCertificates: hgp HX inl
-- statement:
--   The four blocks, described entrywise (`rfl` level).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGP.lean#L75-L77
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGP.lean#L75-L77

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}

theorem QECCertificates.hgpHX_inl (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (x : Fin r₁ × Fin n₂) (ab : Fin n₁ × Fin n₂) :
    hgpHX H₁ H₂ x (Sum.inl ab) = H₁ x.1 ab.1 * (if x.2 = ab.2 then 1 else 0) := by sorry
