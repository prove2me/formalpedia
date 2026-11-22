-- Prove2me | Theorems.Thm_QECCertificates_LRAT_scan_singleton
-- name    : QECCertificates.LRAT.scan_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:45.464506+00:00
-- url     : https://prove2.me/theorems/294a17bb-4d4a-4cb0-a2cd-4bee75707eaf
-- title:
--   LRAT: scan singleton
-- statement:
--   `scan a D = [l]` implies that `l ∈ D` and that every other literal of `D` is false.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/LRAT.lean#L114-L124
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/LRAT.lean#L114-L124

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

theorem QECCertificates.LRAT.scan_singleton {a : PAssign} {D : Clause} {l : Lit} (h : scan a D = [l]) :
    l ∈ D ∧ ∀ l' ∈ D, l' ≠ l → litFree a l' = false := by sorry
