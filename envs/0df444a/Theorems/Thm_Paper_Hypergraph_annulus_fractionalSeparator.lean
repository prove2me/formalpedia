-- Prove2me | Theorems.Thm_Paper_Hypergraph_annulus_fractionalSeparator
-- name    : Paper.Hypergraph.annulus_fractionalSeparator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:02:01.417523+00:00
-- url     : https://prove2.me/theorems/203255f5-3ec5-4acd-a078-57792885fab5
-- title:
--   Hypergraph: annulus fractional Separator
-- statement:
--   Observation 5.8 in the range used by the repaired cut-off lemma.
--   The hypothesis q < (b-a)/2 also ensures that the demand is at most one.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingGeometry.lean#L129-L174
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingGeometry.lean#L129-L174

import Definitions.Def_Paper_RoundingEstimates
import Definitions.Def_Paper_RoundingGeometry
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.annulus_fractionalSeparator (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {c : ℕ} (hc : c ∈ H.vertices)
    {a b q : ℝ} (hq : ∀ v ∈ H.vertices, x v ≤ q) (hgap : q < (b - a) / 2)
    (hq0 : 0 ≤ q) :
    let d := H.vertexDistance x c
    let A := H.vertices.filter (fun v => d v ≤ a)
    let B := H.vertices.filter (fun v => b < d v)
    let z := fun v => if a < d v ∧ d v ≤ b then x v / (b - a - q) else 0
    H.FractionalSeparator A B z := by sorry
