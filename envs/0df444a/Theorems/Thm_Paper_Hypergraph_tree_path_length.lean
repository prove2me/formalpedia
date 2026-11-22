-- Prove2me | Theorems.Thm_Paper_Hypergraph_tree_path_length
-- name    : Paper.Hypergraph.tree_path_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:22.06279+00:00
-- url     : https://prove2.me/theorems/a40e2385-26d8-4ce7-9102-2ecbbd921517
-- title:
--   Hypergraph: tree path length
-- statement:
--   In a tree every simple path has shortest length.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1140-L1146
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1140-L1146

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.tree_path_length {V : Type*} {G : SimpleGraph V} (hG : G.IsTree)
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) : p.length = G.dist u v := by sorry
