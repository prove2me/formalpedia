-- Prove2me | Theorems.Thm_QECCertificates_blockL_rows_mem_of_H1Ker_trivial
-- name    : QECCertificates.blockL_rows_mem_of_H1Ker_trivial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:54:34.997343+00:00
-- url     : https://prove2.me/theorems/16773cc0-e6f1-4066-b833-a136a9b02c1f
-- title:
--   QECCertificates: block L rows mem of H1 Ker trivial
-- statement:
--   **Row cleaning (branch $\ker H_1=0$)**: when $H_1$ is injective, every row of `blockL v` lies in
--   the row space of $H_2$ **unconditionally**.
--
--   This is isomorphic to `blockL_rows_mem_of_small`, except that the "contradiction with $d_1$" step
--   is replaced by **injectivity**: the identity of that step already sends $u:=U z$ into $\ker H_1$,
--   so $u=0$; neither $u\ne 0$ nor a weight hypothesis is needed.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L648-L660
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L648-L660

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

theorem QECCertificates.blockL_rows_mem_of_H1Ker_trivial
    {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)} {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hcomp : H₁ * blockL v = blockR v * H₂)
    (hT : ∀ u : Vec n₁, H₁ *ᵥ u = 0 → u = 0) (a : Fin n₁) :
    (fun b => blockL v a b) ∈ spanL (matRowList H₂) := by sorry
