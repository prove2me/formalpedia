-- Prove2me | Theorems.Thm_QECCertificates_dot_eq_zero_of_mem_kerL_of_mem_spanL
-- name    : QECCertificates.dot_eq_zero_of_mem_kerL_of_mem_spanL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:54:18.43097+00:00
-- url     : https://prove2.me/theorems/92368836-f682-4c1a-9252-ff2cfbe1fff7
-- title:
--   QECCertificates: dot eq zero of mem ker L of mem span L
-- statement:
--   A kernel vector is orthogonal to the whole row space.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L204-L213
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L204-L213

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

theorem QECCertificates.dot_eq_zero_of_mem_kerL_of_mem_spanL {n : ℕ} {L : List (Vec n)} {z u : Vec n}
    (hz : z ∈ kerL L) (hu : u ∈ spanL L) : u ⬝ᵥ z = 0 := by sorry
