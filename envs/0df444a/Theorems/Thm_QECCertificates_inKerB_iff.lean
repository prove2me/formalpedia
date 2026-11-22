-- Prove2me | Theorems.Thm_QECCertificates_inKerB_iff
-- name    : QECCertificates.inKerB_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:45:52.383995+00:00
-- url     : https://prove2.me/theorems/7456129b-4a1c-4c6a-9a88-73383ae06372
-- title:
--   QECCertificates: in Ker B iff
-- statement:
--   **Semantic equivalence of the kernel test**: `inKerB` reports true exactly when `x`
--   lies in the kernel as LeanQEC defines it.
--
--   The bridging lemma is LeanQEC's own `mem_ker_iff_dotProd_rows_eq_zero`, so the computable
--   test and the upstream semantics are connected with **no intermediate layer** and no
--   additional trusted assumption.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Membership.lean#L218-L233
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Membership.lean#L218-L233

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

theorem QECCertificates.inKerB_iff {k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) (x : Vec n) :
    inKerB M x = true ↔ x ∈ LinearMap.ker M.toLin' := by sorry
