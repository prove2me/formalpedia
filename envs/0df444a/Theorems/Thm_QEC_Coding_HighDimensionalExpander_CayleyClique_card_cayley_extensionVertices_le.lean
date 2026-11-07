-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CayleyClique_card_cayley_extensionVertices_le
-- name    : QEC.Coding.HighDimensionalExpander.CayleyClique.card_cayley_extensionVertices_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:51:54.621891+00:00
-- url     : https://prove2.me/theorems/a366b70e-739e-4d27-93a8-a1b324722bcc
-- title:
--   Cayley Clique: card cayley extension Vertices le
-- statement:
--   The number of one-vertex cofaces of a nonempty Cayley-clique face is
--   bounded directly by twice the number of supplied generators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/CayleyClique.lean#L249-L254
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/CayleyClique.lean#L249-L254

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
variable {Γ : Type u} [Group Γ]
variable [Fintype Γ] [DecidableEq Γ]

theorem QEC.Coding.HighDimensionalExpander.CayleyClique.card_cayley_extensionVertices_le
    (S : Finset Γ) (s : Finset Γ) {x : Γ} (hx : x ∈ s) :
    (extensionVertices (cayleyCliqueComplex (S : Set Γ)) s).card ≤ 2 * S.card := by sorry
