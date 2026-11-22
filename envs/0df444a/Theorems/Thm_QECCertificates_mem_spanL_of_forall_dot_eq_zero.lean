-- Prove2me | Theorems.Thm_QECCertificates_mem_spanL_of_forall_dot_eq_zero
-- name    : QECCertificates.mem_spanL_of_forall_dot_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:46:25.651799+00:00
-- url     : https://prove2.me/theorems/dde70358-2a86-4357-8224-03846274e61a
-- title:
--   QECCertificates: mem span L of forall dot eq zero
-- statement:
--   **Decidable form of the separation lemma**: a vector orthogonal to the whole kernel lies in the
--   row space.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L287-L292
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L287-L292

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

theorem QECCertificates.mem_spanL_of_forall_dot_eq_zero {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2))
    {y : Vec k} (h : ∀ z : Vec k, M *ᵥ z = 0 → y ⬝ᵥ z = 0) :
    y ∈ spanL (matRowList M) := by sorry
