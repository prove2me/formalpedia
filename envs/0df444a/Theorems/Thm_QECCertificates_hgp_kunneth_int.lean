-- Prove2me | Theorems.Thm_QECCertificates_hgp_kunneth_int
-- name    : QECCertificates.hgp_kunneth_int
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:55:44.021139+00:00
-- url     : https://prove2.me/theorems/81a46a14-3986-4ec6-8e2c-3f18bfcd5e1b
-- title:
--   QECCertificates: hgp kunneth int
-- statement:
--   **Dimension tensor formula (integer form)**: rewrite `k = n - rank H_X - rank H_Z`
--   additively and do the polynomial arithmetic over `ℤ` (`nlinarith`), which avoids truncated
--   subtraction in `ℕ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPKunneth.lean#L255-L267
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPKunneth.lean#L255-L267

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KunnethCore
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPTranspose
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPKunneth
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {p q r s : ℕ} {r₁ n₁ r₂ n₂ : ℕ}

theorem QECCertificates.hgp_kunneth_int (A : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (B : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) :
    ((hgpHX A B).rank : ℤ) + ((hgpHZ A B).rank : ℤ)
      + (((n₁ : ℤ) - A.rank) * ((n₂ : ℤ) - B.rank)
        + ((r₁ : ℤ) - A.rank) * ((r₂ : ℤ) - B.rank))
      = (n₁ : ℤ) * n₂ + (r₁ : ℤ) * r₂ := by sorry
