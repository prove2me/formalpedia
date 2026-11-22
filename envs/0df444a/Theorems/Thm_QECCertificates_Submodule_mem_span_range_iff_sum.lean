-- Prove2me | Theorems.Thm_QECCertificates_Submodule_mem_span_range_iff_sum
-- name    : QECCertificates.Submodule.mem_span_range_iff_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:22.435039+00:00
-- url     : https://prove2.me/theorems/6dc360ad-caec-49d6-a9d8-1fc147800e22
-- title:
--   Submodule: mem span range iff sum
-- statement:
--   The Submodule construction uses the mem span range iff sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/RowspaceKernel.lean#L60-L77
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/RowspaceKernel.lean#L60-L77

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

theorem QECCertificates.Submodule.mem_span_range_iff_sum {α : Type*} {n : ℕ} (x : Fin n → (ZMod 2)) (v : α → Fin n →
    (ZMod 2))
  : x ∈ Submodule.span (ZMod 2) (Set.range v) ↔ ∃ S : Finset α, ∑ s ∈ S, v s = x := by sorry
