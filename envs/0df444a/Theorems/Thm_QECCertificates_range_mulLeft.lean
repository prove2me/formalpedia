-- Prove2me | Theorems.Thm_QECCertificates_range_mulLeft
-- name    : QECCertificates.range_mulLeft
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:55:26.430674+00:00
-- url     : https://prove2.me/theorems/6b9148e5-0c2e-4392-9dd5-7162fe65b4c3
-- title:
--   QECCertificates: range mul Left
-- statement:
--   **The image of the left block is the column-constraint space**: the image of `M ↦ A·M`
--   consists exactly of the matrices whose every column lies in the column space of `A`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPKunneth.lean#L101-L121
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPKunneth.lean#L101-L121

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

theorem QECCertificates.range_mulLeft (A : Matrix (Fin p) (Fin q) (ZMod 2)) :
    LinearMap.range (mulLeft (s := s) A) = colsSub (LinearMap.range A.mulVecLin) := by sorry
