-- Prove2me | Theorems.Thm_QECCertificates_sum_id_dotProduct_eq
-- name    : QECCertificates.sum_id_dotProduct_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:41:37.662802+00:00
-- url     : https://prove2.me/theorems/4916341d-81d4-43b9-8692-309c44dd9e4d
-- title:
--   QECCertificates: sum id dot Product eq
-- statement:
--   The QECCertificates construction uses the sum id dot Product eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/RowspaceKernel.lean#L205-L210
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/RowspaceKernel.lean#L205-L210

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

theorem QECCertificates.sum_id_dotProduct_eq {n : ℕ} (S : Finset (Fin n → ZMod 2)) (x : Fin n → ZMod 2) :
  S.sum id ⬝ᵥ x = S.sum (fun s => s ⬝ᵥ x) := by sorry
