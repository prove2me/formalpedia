-- Prove2me | Theorems.Thm_QECCertificates_wt_le_of_mem_lightVecs
-- name    : QECCertificates.wt_le_of_mem_lightVecs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:12:31.264267+00:00
-- url     : https://prove2.me/theorems/81667500-8074-4d44-b2cf-d2648aa23962
-- title:
--   QECCertificates: wt le of mem light Vecs
-- statement:
--   **Soundness**: `lightVecs` contains only vectors of weight $\le w$, the other half of
--   the coverage statement `mem_lightVecs`.
--
--   With both halves, the claim that the candidate set is empty is closed in both directions:
--   coverage says nothing is missed, soundness says everything that is left really is light.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/WeightEnum.lean#L215-L254
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/WeightEnum.lean#L215-L254

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.wt_le_of_mem_lightVecs : ∀ (n w : ℕ) (v : Vec n), v ∈ lightVecs n w → wtRec n v ≤ w := by sorry
