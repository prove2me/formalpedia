-- Prove2me | Theorems.Thm_QECCertificates_kerL_le_spanL_kerBasis
-- name    : QECCertificates.kerL_le_spanL_kerBasis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:53:11.970806+00:00
-- url     : https://prove2.me/theorems/4db1aeca-f4c2-483a-b897-4af488c1ca1c
-- title:
--   QECCertificates: ker L le span L ker Basis
-- statement:
--   **Completeness direction**: every vector in the kernel is a linear combination of the
--   kernel generators.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L336-L383
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L336-L383

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.kerL_le_spanL_kerBasis {D : List (PivRow n)} (hD : IsReduced D) :
    kerL (rowList D) ≤ spanL (kerBasis D) := by sorry
