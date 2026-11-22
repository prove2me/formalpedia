-- Prove2me | Theorems.Thm_QECCertificates_LRAT_sum_indicator_eq_cntS
-- name    : QECCertificates.LRAT.sum_indicator_eq_cntS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:00:45.446366+00:00
-- url     : https://prove2.me/theorems/7a7de855-01f9-4a2f-bd6a-b64ee99e242e
-- title:
--   LRAT: sum indicator eq cnt S
-- statement:
--   The sum of indicators is the count: summing the indicator function over a support list equals
--   the
--   count of the assignment.
--
--   This is where `hrn` (no duplicates) is used: `dotS` counts multiplicities, while `Finset` does
--   not.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L119-L139
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L119-L139

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.sum_indicator_eq_cntS (σ : Assign) {n : ℕ} {r : List Nat}
    (hr : ∀ t ∈ r, t < n) (hrn : r.Nodup) :
    (∑ i : Fin n, (if (i : ℕ) ∈ r then (if σ i.val then (1 : ZMod 2) else 0) else 0))
      = ((cntS σ r : ℕ) : ZMod 2) := by sorry
