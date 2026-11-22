-- Prove2me | Theorems.Thm_QECCertificates_min_weight_ker_not_mem_rowspace_pos
-- name    : QECCertificates.min_weight_ker_not_mem_rowspace_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:23.335781+00:00
-- url     : https://prove2.me/theorems/64650f95-1d08-41fb-87f6-3f35ea3a56cb
-- title:
--   QECCertificates: min weight ker not mem rowspace pos
-- statement:
--   The QECCertificates construction uses the min weight ker not mem rowspace pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/RowspaceKernel.lean#L91-L106
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/RowspaceKernel.lean#L91-L106

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

theorem QECCertificates.min_weight_ker_not_mem_rowspace_pos {n k₁ k₂ : ℕ}
  {M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2)} {M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)} :
  0 < minWeightKernelOutsideRowSpace M₁ M₂ := by sorry
