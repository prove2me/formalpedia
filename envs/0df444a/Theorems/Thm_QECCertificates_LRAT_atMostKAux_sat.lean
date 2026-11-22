-- Prove2me | Theorems.Thm_QECCertificates_LRAT_atMostKAux_sat
-- name    : QECCertificates.LRAT.atMostKAux_sat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:58:23.818509+00:00
-- url     : https://prove2.me/theorems/904268e1-2a62-4c1f-8fdb-575e7e03a333
-- title:
--   LRAT: at Most KAux sat
-- statement:
--   **Soundness of the counter**: all clauses satisfied implies that the number of true
--   variables is at most `k`.
--
--   The invariant is: at least `j` of the first `i` variables are true implies that the slot
--   `(i,j)` is true. The induction runs along the list of variables (`pre` is the prefix already
--   processed and `suf` the remainder), so the step needs only `List.filter_append` and not the
--   index bookkeeping of `List.take`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L278-L382
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L278-L382

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.atMostKAux_sat {σ : Assign} {s : Nat → Nat → Option Nat} {k : Nat}
    (hok : SlotOK s k) :
    ∀ (pre suf : List Nat),
      (∀ j, 1 ≤ j → j ≤ min pre.length (k + 1) → j ≤ cntS σ pre →
        ∃ v, s pre.length j = some v ∧ σ v = true) →
      (∀ C ∈ atMostKAux s k pre suf, SatClause σ C) →
      cntS σ (pre ++ suf) ≤ k := by sorry
