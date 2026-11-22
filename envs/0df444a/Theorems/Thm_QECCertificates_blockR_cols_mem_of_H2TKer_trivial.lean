-- Prove2me | Theorems.Thm_QECCertificates_blockR_cols_mem_of_H2TKer_trivial
-- name    : QECCertificates.blockR_cols_mem_of_H2TKer_trivial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:54:39.533199+00:00
-- url     : https://prove2.me/theorems/1ee589c2-b793-4eb4-b49b-139dc97e693f
-- title:
--   QECCertificates: block R cols mem of H2 TKer trivial
-- statement:
--   **Column cleaning (branch $\ker H_2^\top=0$)**: isomorphic to `blockR_cols_mem_of_small`, but
--       the
--   "contradiction with $d_2^\top$" step is replaced by **injectivity**: the identity already sends
--   $y:=R^\top w$ into $\ker H_2^\top$, so $y=0$.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L691-L707
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L691-L707

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}

theorem QECCertificates.blockR_cols_mem_of_H2TKer_trivial
    {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)} {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hcomp : H₁ * blockL v = blockR v * H₂)
    (hT : ∀ u : Vec r₂, H₂.transpose *ᵥ u = 0 → u = 0) (t : Fin r₂) :
    (fun i => blockR v i t) ∈ spanL (colList H₁) := by sorry
