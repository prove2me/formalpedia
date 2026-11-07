-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CayleyClique_neighborVertices_schreier_subset_candidates
-- name    : QEC.Coding.HighDimensionalExpander.CayleyClique.neighborVertices_schreier_subset_candidates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:58:08.424447+00:00
-- url     : https://prove2.me/theorems/026bdb35-eed1-4850-89ee-8efb112396d1
-- title:
--   Cayley Clique: neighbor Vertices schreier subset candidates
-- statement:
--   The Cayley Clique construction uses the neighbor Vertices schreier subset candidates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/CayleyClique.lean#L329-L342
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/CayleyClique.lean#L329-L342

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
variable [Fintype X] [DecidableEq X] [DecidableEq Γ]
omit [DecidableEq Γ]

theorem QEC.Coding.HighDimensionalExpander.CayleyClique.neighborVertices_schreier_subset_candidates (S : Finset Γ) (x : X) :
    neighborVertices (schreierGraph (X := X) (S : Set Γ)) x ⊆
      schreierNeighborCandidates S x := by sorry
