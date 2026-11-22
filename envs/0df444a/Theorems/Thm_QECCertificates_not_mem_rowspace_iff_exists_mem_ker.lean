-- Prove2me | Theorems.Thm_QECCertificates_not_mem_rowspace_iff_exists_mem_ker
-- name    : QECCertificates.not_mem_rowspace_iff_exists_mem_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:41:34.587853+00:00
-- url     : https://prove2.me/theorems/8b6f3282-27ad-4efb-b444-b204593c6421
-- title:
--   QECCertificates: not mem rowspace iff exists mem ker
-- statement:
--   The QECCertificates construction uses the not mem rowspace iff exists mem ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/RowspaceKernel.lean#L168-L175
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/RowspaceKernel.lean#L168-L175

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

theorem QECCertificates.not_mem_rowspace_iff_exists_mem_ker {n k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) (x : Fin
    n → (ZMod 2)) :
  x ∉ M.certificateRowSpace ↔ ∃ y ∈ (LinearMap.ker M.toLin'), y ⬝ᵥ x = 1 := by sorry
