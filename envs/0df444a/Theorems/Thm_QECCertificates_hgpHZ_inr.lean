-- Prove2me | Theorems.Thm_QECCertificates_hgpHZ_inr
-- name    : QECCertificates.hgpHZ_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:45:05.174822+00:00
-- url     : https://prove2.me/theorems/a34155f3-3b42-4913-b8d2-547724ba9b36
-- title:
--   QECCertificates: hgp HZ inr
-- statement:
--   The QECCertificates construction uses the hgp HZ inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGP.lean#L87-L89
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGP.lean#L87-L89

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}

theorem QECCertificates.hgpHZ_inr (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (x : Fin n₁ × Fin r₂) (st : Fin r₁ × Fin r₂) :
    hgpHZ H₁ H₂ x (Sum.inr st) = H₁ st.1 x.1 * (if x.2 = st.2 then 1 else 0) := by sorry
