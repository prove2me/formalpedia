-- Prove2me | Theorems.Thm_QECCertificates_hgp_kunneth
-- name    : QECCertificates.hgp_kunneth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:09:08.371365+00:00
-- url     : https://prove2.me/theorems/5a402be2-02e4-4bc4-991f-ffe91a3a06fc
-- title:
--   QECCertificates: hgp kunneth
-- statement:
--   **Dimension tensor formula for HGP (Künneth)**: the number of logical qubits
--   $k = n - \operatorname{rank}H_X - \operatorname{rank}H_Z$ is exactly
--   $k_1k_2 + k_1^\top k_2^\top$ (the sum of the products of the kernel dimensions of the two
--   classical codes).
--
--   This is the last piece: the distance side (the third part together with the dual side) and
--   the dimension side (this theorem) together give the HGP family parameters for $n\ge144$ a
--   **structural assertion that does not rely on enumeration**.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPKunneth.lean#L277-L320
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPKunneth.lean#L277-L320

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

theorem QECCertificates.hgp_kunneth (A : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (B : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) :
    (n₁ * n₂ + r₁ * r₂) - (hgpHX A B).rank - (hgpHZ A B).rank
      = (n₁ - A.rank) * (n₂ - B.rank) + (r₁ - A.rank) * (r₂ - B.rank) := by sorry
