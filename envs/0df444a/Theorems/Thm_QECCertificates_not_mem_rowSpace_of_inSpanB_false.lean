-- Prove2me | Theorems.Thm_QECCertificates_not_mem_rowSpace_of_inSpanB_false
-- name    : QECCertificates.not_mem_rowSpace_of_inSpanB_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:13:49.036989+00:00
-- url     : https://prove2.me/theorems/49cc2e2a-b54f-44e8-bbb3-86c8ec8917ba
-- title:
--   QECCertificates: not mem row Space of in Span B false
-- statement:
--   Non-membership in the row space from the full row-reduction decision procedure.
--
--   **Note**: this lemma runs `rowReduce` internally and is expensive on wide matrices; for
--   those, use `not_mem_rowSpace_of_dualCheck`, the dual witness route, instead.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LowerBound.lean#L272-L275
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LowerBound.lean#L272-L275

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Membership
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
public import Definitions.Def_LeanPool_QECCertificates_GF2_LowerBound
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.not_mem_rowSpace_of_inSpanB_false {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2))
    {v : Vec n} (h : inSpanB (List.ofFn fun i => M i) v = false) : v ∉ M.certificateRowSpace := by sorry
