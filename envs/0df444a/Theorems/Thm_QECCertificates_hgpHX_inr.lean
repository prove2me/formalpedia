-- Prove2me | Theorems.Thm_QECCertificates_hgpHX_inr
-- name    : QECCertificates.hgpHX_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:47:59.409157+00:00
-- url     : https://prove2.me/theorems/2d8cd0a0-52b8-49cc-9f5d-62c84bf3d1c3
-- title:
--   QECCertificates: hgp HX inr
-- statement:
--   The QECCertificates construction uses the hgp HX inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGP.lean#L79-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGP.lean#L79-L81

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}

theorem QECCertificates.hgpHX_inr (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (x : Fin r₁ × Fin n₂) (st : Fin r₁ × Fin r₂) :
    hgpHX H₁ H₂ x (Sum.inr st) = (if x.1 = st.1 then 1 else 0) * H₂ st.2 x.2 := by sorry
