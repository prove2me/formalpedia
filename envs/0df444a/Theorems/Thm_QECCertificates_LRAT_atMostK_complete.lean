-- Prove2me | Theorems.Thm_QECCertificates_LRAT_atMostK_complete
-- name    : QECCertificates.LRAT.atMostK_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:59.60074+00:00
-- url     : https://prove2.me/theorems/7b08b121-88b4-4a0a-96e5-8fdffe308473
-- title:
--   LRAT: at Most K complete
-- statement:
--   **Completeness of the sequential counter**: if at most `k` variables are true, then
--   there exists an assignment satisfying all the counter clauses that agrees with the given
--   assignment on the input variables.
--
--   The induction follows the traversal of `atMostKAux` (`pre` is the prefix already processed
--   and `suf` the remainder), writing the slot block of that row into the assignment at each
--   step. The returned assignment has two properties that the outer argument uses: it **agrees
--   with the original assignment below `c + slotBase k (pre.length + 1)`** (the slots filled by
--   earlier rows are not overwritten by later ones), and it **characterizes the slot values of
--   the last row** (the next step uses this as its `hprev`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L739-L906
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L739-L906

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.atMostK_complete {k c : Nat} {xs : List Nat} {σ : Assign}
    (hc : ∀ t ∈ xs, t < c) (hcnt : cntS σ xs ≤ k) :
    ∃ τ : Assign, (∀ t, t < c → τ t = σ t) ∧
      ∀ C ∈ atMostK (slotVar c k) k xs, SatClause τ C := by sorry
