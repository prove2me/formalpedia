-- Prove2me | Theorems.Thm_Paper_Hypergraph_TreeDecomposition_walk_avoiding
-- name    : Paper.Hypergraph.TreeDecomposition.walk_avoiding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:33.635182+00:00
-- url     : https://prove2.me/theorems/43e3b74a-5ae8-4aaf-bf3e-1e206ac0241d
-- title:
--   Tree Decomposition: walk avoiding
-- statement:
--   Bags meeting one residual primal component remain connected after deleting the root bag.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1181-L1202
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1181-L1202

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.TreeDecomposition.walk_avoiding {H : Hypergraph} {n : ℕ}
    (D : H.TreeDecomposition n) (t : Fin (n + 1)) {v w : ℕ}
    (p : (H.induce (H.vertices \ D.bag t)).primal.Walk v w)
    (hv : v ∈ (H.induce (H.vertices \ D.bag t)).vertices)
    {a b : Fin (n + 1)} (ha : v ∈ D.bag a) (hb : w ∈ D.bag b)
    (hat : a ≠ t) (hbt : b ≠ t) :
    (D.tree.induce {s | s ≠ t}).Reachable ⟨a, hat⟩ ⟨b, hbt⟩ := by sorry
