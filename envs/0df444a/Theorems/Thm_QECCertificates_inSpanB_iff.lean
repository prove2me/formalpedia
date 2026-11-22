-- Prove2me | Theorems.Thm_QECCertificates_inSpanB_iff
-- name    : QECCertificates.inSpanB_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:56:28.811128+00:00
-- url     : https://prove2.me/theorems/919dee0f-8b9e-4da0-b203-cc4ee5bab926
-- title:
--   QECCertificates: in Span B iff
-- statement:
--   **Semantic equivalence of the membership test**: the computable test and subspace
--   membership agree exactly.
--
--   This is the **single entry point** for handing distance and rank questions to the kernel:
--   any Boolean conclusion obtained by `decide` can be translated back into the language of
--   `Submodule` through this theorem, and so be connected to the existing theorems of
--   LeanQEC.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Membership.lean#L186-L187
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Membership.lean#L186-L187

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Membership
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.inSpanB_iff (L : List (Vec n)) (v : Vec n) : inSpanB L v = true ↔ v ∈ spanL L := by sorry
