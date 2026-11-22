-- Prove2me | Theorems.Thm_QECCertificates_rank_hgpHZ_add
-- name    : QECCertificates.rank_hgpHZ_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:55:34.686824+00:00
-- url     : https://prove2.me/theorems/4175b162-6033-49bb-8984-19156815273f
-- title:
--   QECCertificates: rank hgp HZ add
-- statement:
--   **The rank of `H_Z`**: the same shape as `rank_hgpHX_add`, with `n₂ ↦ r₂` and
--   `r₁ ↦ n₁`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPKunneth.lean#L242-L248
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPKunneth.lean#L242-L248

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

theorem QECCertificates.rank_hgpHZ_add (A : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (B : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) :
    (hgpHZ A B).rank + A.rank * B.rank = A.rank * r₂ + B.rank * n₁ := by sorry
