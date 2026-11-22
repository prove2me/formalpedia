-- Prove2me | Theorems.Thm_QECCertificates_LRAT_all_of_mem_bounds
-- name    : QECCertificates.LRAT.all_of_mem_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:36.479965+00:00
-- url     : https://prove2.me/theorems/21d6f93a-2f3c-4b7d-8273-83d57d7498ee
-- title:
--   LRAT: all of mem bounds
-- statement:
--   Turn a bound in `List.all` form into a pointwise form. The quantifier shape `∀ r ∈ L, …` is
--   not one
--   the kernel can decide directly, so the three encoder-side facts are first written with `all` and
--   then converted into theorem hypotheses here.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L235-L239
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L235-L239

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.all_of_mem_bounds {n : ℕ} {L : List (List Nat)}
    (h : (L.all fun r => r.all fun t => decide (t < n)) = true) :
    ∀ r ∈ L, ∀ t ∈ r, t < n := by sorry
