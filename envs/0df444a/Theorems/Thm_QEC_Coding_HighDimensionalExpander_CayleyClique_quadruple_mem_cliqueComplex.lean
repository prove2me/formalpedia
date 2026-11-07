-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CayleyClique_quadruple_mem_cliqueComplex
-- name    : QEC.Coding.HighDimensionalExpander.CayleyClique.quadruple_mem_cliqueComplex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:50:35.231082+00:00
-- url     : https://prove2.me/theorems/bb5dc10b-358d-4a83-8df7-dc9375cdf987
-- title:
--   Cayley Clique: quadruple mem clique Complex
-- statement:
--   Four pairwise adjacent vertices form an actual tetrahedral face of the
--   clique complex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/CayleyClique.lean#L66-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/CayleyClique.lean#L66-L93

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

theorem QEC.Coding.HighDimensionalExpander.CayleyClique.quadruple_mem_cliqueComplex
    [DecidableEq V] (G : SimpleGraph V) {a b c d : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (had : G.Adj a d)
    (hbc : G.Adj b c) (hbd : G.Adj b d) (hcd : G.Adj c d) :
    {a, b, c, d} ∈ cliqueComplex G := by sorry
