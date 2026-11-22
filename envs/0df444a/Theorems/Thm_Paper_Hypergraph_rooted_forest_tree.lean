-- Prove2me | Theorems.Thm_Paper_Hypergraph_rooted_forest_tree
-- name    : Paper.Hypergraph.rooted_forest_tree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:11.76486+00:00
-- url     : https://prove2.me/theorems/7a958919-f008-4b3d-b324-c83e51e21c46
-- title:
--   Hypergraph: rooted forest tree
-- statement:
--   Join a family of trees by edges from one designated root to all other roots.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1784-L1837
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1784-L1837

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.rooted_forest_tree {I : Type*} {V : I → Type*}
    (G : ∀ i, SimpleGraph (V i)) (hG : ∀ i, (G i).IsTree)
    (root : ∀ i, V i) (o : I) :
    ∃ F : SimpleGraph (Sigma V), F.IsTree ∧ forestGraph G ≤ F ∧
      ∀ i, i ≠ o → F.Adj ⟨o, root o⟩ ⟨i, root i⟩ := by sorry
