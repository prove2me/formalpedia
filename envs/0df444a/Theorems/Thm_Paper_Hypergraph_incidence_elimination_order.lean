-- Prove2me | Theorems.Thm_Paper_Hypergraph_incidence_elimination_order
-- name    : Paper.Hypergraph.incidence_elimination_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:48.147957+00:00
-- url     : https://prove2.me/theorems/cfd3e2da-9970-43aa-bfb3-a3492ae67416
-- title:
--   Hypergraph: incidence elimination order
-- statement:
--   An elimination order of the incidence graph with at most μ later neighbors.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingDegeneracy.lean#L11-L61
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingDegeneracy.lean#L11-L61

import Definitions.Def_Paper_RoundingAveraging
import Definitions.Def_Paper_RoundingDegeneracy
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset MeasureTheory
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.incidence_elimination_order (H : Hypergraph) :
    ∃ rank : ℕ ⊕ ℕ → ℕ, Set.InjOn rank (↑H.incidenceVertices : Set (ℕ ⊕ ℕ)) ∧
      ∀ v ∈ H.incidenceVertices,
        (H.incidenceVertices.filter (fun w => H.incidence.Adj v w ∧ rank v < rank w)).card ≤ H.degeneracy := by sorry
