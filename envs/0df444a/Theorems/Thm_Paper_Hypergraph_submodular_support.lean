-- Prove2me | Theorems.Thm_Paper_Hypergraph_submodular_support
-- name    : Paper.Hypergraph.submodular_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:56:43.122683+00:00
-- url     : https://prove2.me/theorems/8343ddb5-186b-476c-9a21-2de59014bc10
-- title:
--   Hypergraph: submodular support
-- statement:
--   The greedy supporting modular function for a finite polymatroid.
--   The induction contracts one vertex; the resulting weights are supported on U.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L334-L413
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L334-L413

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.submodular_support (U : Finset ℕ) (b : Finset ℕ → ℝ)
    (h0 : b ∅ = 0)
    (hm : ∀ A ⊆ U, ∀ B ⊆ U, A ⊆ B → b A ≤ b B)
    (hs : ∀ A ⊆ U, ∀ B ⊆ U, b (A ∪ B) + b (A ∩ B) ≤ b A + b B) :
    ∃ w : ℕ → ℝ, (∀ v, 0 ≤ w v) ∧ (∀ v ∉ U, w v = 0) ∧
      modularValue w U = b U ∧ ∀ A ⊆ U, modularValue w A ≤ b A := by sorry
