-- Prove2me | Theorems.Thm_QECCertificates_LRAT_scanAux_spec
-- name    : QECCertificates.LRAT.scanAux_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:41:33.39492+00:00
-- url     : https://prove2.me/theorems/1c7dcc4b-5ddd-4064-a19c-2ee6fcf9fc20
-- title:
--   LRAT: scan Aux spec
-- statement:
--   The LRAT construction uses the scan Aux spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/LRAT.lean#L71-L100
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/LRAT.lean#L71-L100

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

theorem QECCertificates.LRAT.scanAux_spec (a : PAssign) (D : Clause) (fr : List Lit) :
    ∃ tail : List Lit,
      scanAux a fr D = tail ++ fr ∧
        (∀ l ∈ tail, l ∈ D ∧ litFree a l = true) ∧
        (∀ l ∈ D, litFree a l = true → l ∈ tail) := by sorry
