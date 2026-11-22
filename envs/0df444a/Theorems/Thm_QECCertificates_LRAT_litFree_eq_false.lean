-- Prove2me | Theorems.Thm_QECCertificates_LRAT_litFree_eq_false
-- name    : QECCertificates.LRAT.litFree_eq_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:48.802427+00:00
-- url     : https://prove2.me/theorems/ea66c6ad-771c-4608-b6c9-d3a216454468
-- title:
--   LRAT: lit Free eq false
-- statement:
--   If a literal is not free under the current assignment, then its negation has been
--   assigned.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/LRAT.lean#L128-L134
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/LRAT.lean#L128-L134

module
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic
public import Std.Data.TreeMap.Lemmas
public import Std.Data.DTreeMap.Lemmas
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.litFree_eq_false {a : PAssign} {l : Lit} (h : litFree a l = false)
    {σ : Assign} (hσ : agrees σ a) : σ l.1 = !l.2 := by sorry
