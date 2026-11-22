-- Prove2me | Theorems.Thm_QECCertificates_hgpHX_mulVec_eq_zero_iff
-- name    : QECCertificates.hgpHX_mulVec_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:42:49.605806+00:00
-- url     : https://prove2.me/theorems/e2d684ad-71d1-41b4-b896-7fda409170c5
-- title:
--   QECCertificates: hgp HX mul Vec eq zero iff
-- statement:
--   **Compression identity (X side)**: $H_X v = 0 \iff H_1\,U = R\,H_2$.
--
--   The equality on the right is the statement that $(U, R)$ is a chain map; the whole case
--   analysis of the distance lower bound unfolds from it.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCompression.lean#L178-L194
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCompression.lean#L178-L194

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}

theorem QECCertificates.hgpHX_mulVec_eq_zero_iff (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) :
    hgpHX H₁ H₂ *ᵥ v = 0 ↔ H₁ * blockL v = blockR v * H₂ := by sorry
