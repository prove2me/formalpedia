-- Prove2me | Theorems.Thm_QECCertificates_Matrix_is_ker_for_of_rank_sum_mutually_orth
-- name    : QECCertificates.Matrix.is_ker_for_of_rank_sum_mutually_orth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:39.919161+00:00
-- url     : https://prove2.me/theorems/8f9a1f58-adb0-4d12-a751-62cb83ce5fe4
-- title:
--   Matrix: is ker for of rank sum mutually orth
-- statement:
--   The Matrix construction uses the is ker for of rank sum mutually orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/RowspaceKernel.lean#L333-L359
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/RowspaceKernel.lean#L333-L359

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

theorem QECCertificates.Matrix.is_ker_for_of_rank_sum_mutually_orth
  {k₁ k₂ r₁ r₂ n : ℕ}
  (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
  (hr₁ : r₁ ≤ M₁.rank)
  (hr₂ : r₂ ≤ M₂.rank)
  (hrn : r₁ + r₂ = n)
  (ho : M₁.certificateMutuallyOrthogonalRows M₂) :
  M₂.certificateIsKernelFor M₁ := by sorry
