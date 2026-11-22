-- Prove2me | Theorems.Thm_QECCertificates_hgpHZ_inl
-- name    : QECCertificates.hgpHZ_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:45:00.924327+00:00
-- url     : https://prove2.me/theorems/e3845480-9cb5-46f6-a71f-8cfe7a5a2731
-- title:
--   QECCertificates: hgp HZ inl
-- statement:
--   The QECCertificates construction uses the hgp HZ inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGP.lean#L83-L85
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGP.lean#L83-L85

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}

theorem QECCertificates.hgpHZ_inl (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (x : Fin n₁ × Fin r₂) (ab : Fin n₁ × Fin n₂) :
    hgpHZ H₁ H₂ x (Sum.inl ab) = (if x.1 = ab.1 then 1 else 0) * H₂ x.2 ab.2 := by sorry
