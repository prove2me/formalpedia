-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CayleyClique_map_mem_schreierCliqueComplex_iff
-- name    : QEC.Coding.HighDimensionalExpander.CayleyClique.map_mem_schreierCliqueComplex_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:58:08.29609+00:00
-- url     : https://prove2.me/theorems/cf50db32-ac01-4e13-9e83-ad63159b1b19
-- title:
--   Cayley Clique: map mem schreier Clique Complex iff
-- statement:
--   The Cayley Clique construction uses the map mem schreier Clique Complex iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/CayleyClique.lean#L313-L317
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/CayleyClique.lean#L313-L317

import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CayleyClique
open Finset
universe u v
variable {V : Type u} {W : Type v}
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

theorem QEC.Coding.HighDimensionalExpander.CayleyClique.map_mem_schreierCliqueComplex_iff
    (S : Set Γ) (e : X ≃ X) (h : ∀ g ∈ S, ∀ x, e (g • x) = g • e x)
    (s : Finset X) :
    s.map e.toEmbedding ∈ schreierCliqueComplex S ↔ s ∈ schreierCliqueComplex S := by sorry
