-- Prove2me | Theorems.Thm_Paper_Hypergraph_TreeDecomposition_same_vertex_avoiding
-- name    : Paper.Hypergraph.TreeDecomposition.same_vertex_avoiding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:33.395027+00:00
-- url     : https://prove2.me/theorems/350997de-ddee-4af6-9b66-a8794b3ade9a
-- title:
--   Tree Decomposition: same vertex avoiding
-- statement:
--   The Tree Decomposition construction uses the same vertex avoiding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1169-L1178
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1169-L1178

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.TreeDecomposition.same_vertex_avoiding {H : Hypergraph} {n : ℕ}
    (D : H.TreeDecomposition n) (t : Fin (n + 1)) {v : ℕ} (hv : v ∈ H.vertices)
    (hvt : v ∉ D.bag t) {a b : Fin (n + 1)} (ha : v ∈ D.bag a) (hb : v ∈ D.bag b) :
    (D.tree.induce {s | s ≠ t}).Reachable
      ⟨a, fun h => hvt (h ▸ ha)⟩ ⟨b, fun h => hvt (h ▸ hb)⟩ := by sorry
