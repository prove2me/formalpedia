-- Prove2me | Theorems.Thm_QECCertificates_rank_hgpHX_add
-- name    : QECCertificates.rank_hgpHX_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:26.432937+00:00
-- url     : https://prove2.me/theorems/2f86fa98-f6f9-4a9e-bc51-a1798de48098
-- title:
--   QECCertificates: rank hgp HX add
-- statement:
--   **The rank of `H_X` equals the dimension of the sum of the images of the two blocks**.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPKunneth.lean#L172-L213
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPKunneth.lean#L172-L213

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

theorem QECCertificates.rank_hgpHX_add (A : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (B : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) :
    (hgpHX A B).rank + A.rank * B.rank = A.rank * n₂ + B.rank * r₁ := by sorry
