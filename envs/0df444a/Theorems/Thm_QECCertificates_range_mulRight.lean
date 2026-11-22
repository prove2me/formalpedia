-- Prove2me | Theorems.Thm_QECCertificates_range_mulRight
-- name    : QECCertificates.range_mulRight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:55:22.751989+00:00
-- url     : https://prove2.me/theorems/52339b2e-eb51-40b7-be62-da848727d3f1
-- title:
--   QECCertificates: range mul Right
-- statement:
--   **The image of the right block is the row-constraint space**: the image of `N ↦ N·B`
--   consists exactly of the matrices whose every row lies in the row space of `B`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPKunneth.lean#L125-L147
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPKunneth.lean#L125-L147

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

theorem QECCertificates.range_mulRight (B : Matrix (Fin r) (Fin s) (ZMod 2)) :
    LinearMap.range (mulRight (p := p) B) = rowsSub (Matrix.certificateRowSpace B) := by sorry
