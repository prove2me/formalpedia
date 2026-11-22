-- Prove2me | Theorems.Thm_Paper_Hypergraph_tree_weighted_median
-- name    : Paper.Hypergraph.tree_weighted_median
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:20.28965+00:00
-- url     : https://prove2.me/theorems/160426fa-cf56-4d02-b4e2-48b60b977195
-- title:
--   Hypergraph: tree weighted median
-- statement:
--   A weighted distance minimizer in a finite tree has no heavy branch.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1106-L1137
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1106-L1137

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.tree_weighted_median {V I : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hG : G.IsTree) (E : Finset I) (a : I → V) (w : I → ℝ)
    (_hw : ∀ e ∈ E, 0 ≤ w e) :
    ∃ t, ∀ s, G.Adj t s →
      (∑ e ∈ E.filter (fun e => G.dist t (a e) = G.dist s (a e) + 1), w e) ≤
        (1 / 2 : ℝ) * ∑ e ∈ E, w e := by sorry
