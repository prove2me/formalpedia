-- Prove2me | Theorems.Thm_QECCertificates_zmod2_val_eq_one_of_ne_zero
-- name    : QECCertificates.zmod2_val_eq_one_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:14.245579+00:00
-- url     : https://prove2.me/theorems/400430f7-6807-4c55-b18c-44565bebe664
-- title:
--   QECCertificates: zmod2 val eq one of ne zero
-- statement:
--   The QECCertificates construction uses the zmod2 val eq one of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/RowspaceKernel.lean#L42-L45
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/RowspaceKernel.lean#L42-L45

module
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates

theorem QECCertificates.zmod2_val_eq_one_of_ne_zero (a : ZMod 2) (ha : a ≠ 0) : a.1 = 1 := by sorry
