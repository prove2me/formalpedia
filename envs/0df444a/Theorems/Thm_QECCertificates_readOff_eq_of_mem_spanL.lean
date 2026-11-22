-- Prove2me | Theorems.Thm_QECCertificates_readOff_eq_of_mem_spanL
-- name    : QECCertificates.readOff_eq_of_mem_spanL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:46:01.139879+00:00
-- url     : https://prove2.me/theorems/8906e0b2-1158-4d1f-93e9-2608b830e0a7
-- title:
--   QECCertificates: read Off eq of mem span L
-- statement:
--   **Main lemma (read-off = identity)**: when `D` is mutually reduced, the read-off is the identity
--   map on the row space of `D`.
--
--   The proof follows `Submodule.span_induction`: on a generator, the pivot column of `ri` collapses the
--   sum to a single term (the remaining terms are killed by (R2)); the zero, addition and scalar cases
--   are given by `readOff_add`/`readOff_smul`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Canonical.lean#L97-L117
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Canonical.lean#L97-L117

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.readOff_eq_of_mem_spanL {D : List (PivRow n)} (hD : IsReduced D) {w : Vec n}
    (hw : w ∈ spanL (rowList D)) : readOff D w = w := by sorry
