-- Prove2me | Theorems.Thm_QECCertificates_LRAT_rowOf_range
-- name    : QECCertificates.LRAT.rowOf_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:21.894671+00:00
-- url     : https://prove2.me/theorems/7667ce18-147c-47bb-b73f-740ae8b5e72d
-- title:
--   LRAT: row Of range
-- statement:
--   The all-ones support list reads out as the all-ones vector.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L221-L223
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L221-L223

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.rowOf_range (n : ℕ) : rowOf n (List.range n) = fun _ : Fin n => 1 := by sorry
