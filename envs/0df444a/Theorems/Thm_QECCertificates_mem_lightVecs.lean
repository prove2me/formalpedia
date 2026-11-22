-- Prove2me | Theorems.Thm_QECCertificates_mem_lightVecs
-- name    : QECCertificates.mem_lightVecs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:54.660727+00:00
-- url     : https://prove2.me/theorems/db58aecd-0d25-4c91-9c44-1c130b455ad3
-- title:
--   QECCertificates: mem light Vecs
-- statement:
--   **Coverage**: every vector of weight $\le w$ occurs in `lightVecs n w`.
--
--   The proof follows the recursive structure of `lightVecs` by looking at the last
--   coordinate. If the last coordinate is nonzero then the weight of the prefix must be
--   $\le w$; if it is zero then the prefix need only have weight $\le w+1$. Each case lands in
--   the corresponding half of the enumeration.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/WeightEnum.lean#L177-L206
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/WeightEnum.lean#L177-L206

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.mem_lightVecs : ∀ (n w : ℕ) (v : Vec n), wtRec n v ≤ w → v ∈ lightVecs n w := by sorry
