-- Prove2me | Theorems.Thm_QECCertificates_ex_mem_submodule_non_orth_iff_non_orth_mem_basis
-- name    : QECCertificates.ex_mem_submodule_non_orth_iff_non_orth_mem_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:33.896805+00:00
-- url     : https://prove2.me/theorems/3cc6acff-c180-4c15-aa2d-c4d3391d30ab
-- title:
--   QECCertificates: ex mem submodule non orth iff non orth mem basis
-- statement:
--   A binary vector pairs nontrivially with the span exactly when it does with a generator.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/RowspaceKernel.lean#L178-L198
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/RowspaceKernel.lean#L178-L198

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

theorem QECCertificates.ex_mem_submodule_non_orth_iff_non_orth_mem_basis {n : ℕ}
    (S : Set (Fin n → ZMod 2)) (x : Fin n → ZMod 2) :
    (∃ y ∈ Submodule.span (ZMod 2) S, y ⬝ᵥ x = 1) ↔ ∃ s ∈ S, s ⬝ᵥ x = 1 := by sorry
