-- Prove2me | Theorems.Thm_QECCertificates_Matrix_rank_le_of_submatrix_independent
-- name    : QECCertificates.Matrix.rank_le_of_submatrix_independent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:42.277086+00:00
-- url     : https://prove2.me/theorems/adbfcfa6-2541-4ac9-a466-ed22ef12772d
-- title:
--   Matrix: rank le of submatrix independent
-- statement:
--   The Matrix construction uses the rank le of submatrix independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/RowspaceKernel.lean#L361-L373
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/RowspaceKernel.lean#L361-L373

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

theorem QECCertificates.Matrix.rank_le_of_submatrix_independent
  {k r n : ℕ}
  (M : Matrix (Fin r) (Fin n) (ZMod 2))
  (inds : Fin k → Fin r)
  (_inds_mono : StrictMono inds)
  (h_ind : LinearIndependent (ZMod 2) (M.submatrix inds id)) :
  k ≤ M.rank := by sorry
