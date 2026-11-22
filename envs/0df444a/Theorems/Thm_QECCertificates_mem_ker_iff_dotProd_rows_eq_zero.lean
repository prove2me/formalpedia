-- Prove2me | Theorems.Thm_QECCertificates_mem_ker_iff_dotProd_rows_eq_zero
-- name    : QECCertificates.mem_ker_iff_dotProd_rows_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:41:34.247174+00:00
-- url     : https://prove2.me/theorems/188ea5cc-6485-4dd4-85bc-b378650ef120
-- title:
--   QECCertificates: mem ker iff dot Prod rows eq zero
-- statement:
--   The QECCertificates construction uses the mem ker iff dot Prod rows eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/RowspaceKernel.lean#L108-L116
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/RowspaceKernel.lean#L108-L116

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

theorem QECCertificates.mem_ker_iff_dotProd_rows_eq_zero {n k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) (x : Fin n
    → (ZMod 2)) :
  x ∈ ((LinearMap.ker M.toLin')) ↔ ∀ i, (M i) ⬝ᵥ x = 0 := by sorry
