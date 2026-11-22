-- Prove2me | Theorems.Thm_QECCertificates_blockL_rows_mem_of_H2Ker_trivial
-- name    : QECCertificates.blockL_rows_mem_of_H2Ker_trivial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:54:38.394573+00:00
-- url     : https://prove2.me/theorems/479eaee3-b989-45d2-8f58-a0a06f4d2ac5
-- title:
--   QECCertificates: block L rows mem of H2 Ker trivial
-- statement:
--   **Row cleaning (branch $\ker H_2=0$)**: when $H_2$ is injective the orthogonality hypothesis is
--   **vacuous**: the required $\langle U_{a\cdot},z\rangle=0$ is asked only for $z\in\ker H_2$, where
--   $z=0$ is the only element. (This branch therefore **does not need** the compression identity: the
--   conclusion mentions only `blockL v` and $H_2$.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L666-L673
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L666-L673

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

theorem QECCertificates.blockL_rows_mem_of_H2Ker_trivial
    {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hT : ∀ u : Vec n₂, H₂ *ᵥ u = 0 → u = 0) (a : Fin n₁) :
    (fun b => blockL v a b) ∈ spanL (matRowList H₂) := by sorry
