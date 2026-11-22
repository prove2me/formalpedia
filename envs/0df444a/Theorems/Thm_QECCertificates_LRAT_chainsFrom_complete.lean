-- Prove2me | Theorems.Thm_QECCertificates_LRAT_chainsFrom_complete
-- name    : QECCertificates.LRAT.chainsFrom_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:58:49.06874+00:00
-- url     : https://prove2.me/theorems/a6d22899-e8b4-478b-b658-b09fa25a6bb0
-- title:
--   LRAT: chains From complete
-- statement:
--   **Completeness of a sequence of chains**: if the dot product of every row is `false`,
--   then there exists an assignment that satisfies all the chain clauses at once and agrees with
--   the input below the counter `c`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L308-L370
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L308-L370

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.chainsFrom_complete {f : Nat → Nat} {rows : List (List Nat)}
    (hne : ∀ r ∈ rows, r ≠ []) :
    ∀ (c : Nat) (σ : Assign), (∀ r ∈ rows, ∀ t ∈ r, f t < c) →
      (∀ r ∈ rows, dotS (fun t => σ (f t)) r = false) →
      ∃ τ : Assign, (∀ t, t < c → τ t = σ t) ∧
        ∀ C ∈ (chainsFrom f rows c).1, SatClause τ C := by sorry
