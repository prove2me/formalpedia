-- Prove2me | Theorems.Thm_QECCertificates_ker_dotProduct_rowSpace_eq_zero
-- name    : QECCertificates.ker_dotProduct_rowSpace_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:41:37.769726+00:00
-- url     : https://prove2.me/theorems/9fd3f78f-8b0e-4986-ba59-36fd116647ce
-- title:
--   QECCertificates: ker dot Product row Space eq zero
-- statement:
--   The QECCertificates construction uses the ker dot Product row Space eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/RowspaceKernel.lean#L121-L131
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/RowspaceKernel.lean#L121-L131

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

theorem QECCertificates.ker_dotProduct_rowSpace_eq_zero {n k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2))
    (y : Fin n → ZMod 2) (x : Fin n → ZMod 2)
    (hy : y ∈ LinearMap.ker M.toLin') (hx : x ∈ M.certificateRowSpace) : y ⬝ᵥ x = 0 := by sorry
