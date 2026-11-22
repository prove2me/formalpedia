-- Prove2me | Theorems.Thm_Paper_Hypergraph_tree_branch_distance
-- name    : Paper.Hypergraph.tree_branch_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:26.686832+00:00
-- url     : https://prove2.me/theorems/162ea4a3-c3ad-478d-b2c9-360de617b630
-- title:
--   Hypergraph: tree branch distance
-- statement:
--   Every node reachable from a neighbor while avoiding the root is one step closer
--   from that neighbor than from the root.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1150-L1167
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1150-L1167

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.tree_branch_distance {V : Type*} {G : SimpleGraph V} (hG : G.IsTree)
    {t r u : V} (htr : G.Adj t r) (hu : u ≠ t)
    (hr : (G.induce {v | v ≠ t}).Reachable ⟨r, htr.ne.symm⟩ ⟨u, hu⟩) :
    G.dist t u = G.dist r u + 1 := by sorry
