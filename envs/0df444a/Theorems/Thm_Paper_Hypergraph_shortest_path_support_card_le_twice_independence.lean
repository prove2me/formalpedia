-- Prove2me | Theorems.Thm_Paper_Hypergraph_shortest_path_support_card_le_twice_independence
-- name    : Paper.Hypergraph.shortest_path_support_card_le_twice_independence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:10.823115+00:00
-- url     : https://prove2.me/theorems/fb213d5d-17a0-4876-af7b-31043406709e
-- title:
--   Hypergraph: shortest path support card le twice independence
-- statement:
--   The vertices of a shortest path split into two independent sets.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingIndependence.lean#L16-L64
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingIndependence.lean#L16-L64

import Definitions.Def_Paper_RoundingAveraging
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_Paper_RoundingIndependence
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.shortest_path_support_card_le_twice_independence (H : Hypergraph)
    (Q R : Finset ℕ) {u v : ℕ} (hu : u ∈ (H.induce Q).vertices)
    (p : (H.induce Q).primal.Walk u v) (hp : p.length = (H.induce Q).primal.dist u v)
    {S : Finset ℕ} (hS : ∀ w ∈ S, w ∈ p.support) (hR : S ⊆ R) :
    S.card ≤ 2 * (H.induce R).independenceNumber := by sorry
