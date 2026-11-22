-- Prove2me | Theorems.Thm_QECCertificates_rank_hgpHZ_eq
-- name    : QECCertificates.rank_hgpHZ_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:55:26.889606+00:00
-- url     : https://prove2.me/theorems/dfeb8983-c287-425d-9957-36c270ce91dc
-- title:
--   QECCertificates: rank hgp HZ eq
-- statement:
--   **The rank of `H_Z` equals the rank of `H_X` on the transposed inputs**: the two
--   matrices differ only by the block swap of the columns (`mulVec_swap_eq` from the third
--   part), so their images agree.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPKunneth.lean#L220-L238
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPKunneth.lean#L220-L238

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

theorem QECCertificates.rank_hgpHZ_eq (A : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (B : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) :
    (hgpHZ A B).rank = (hgpHX A.transpose B.transpose).rank := by sorry
