-- Prove2me | Theorems.Thm_Paper_Hypergraph_twoTerminal_degeneracy_rounding
-- name    : Paper.Hypergraph.twoTerminal_degeneracy_rounding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:05:23.69658+00:00
-- url     : https://prove2.me/theorems/dc11bf21-598c-42c2-b3da-f42b361f874d
-- title:
--   Hypergraph: two Terminal degeneracy rounding
-- statement:
--   The degeneracy branch of Theorem 4.1.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingDegeneracy.lean#L268-L287
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingDegeneracy.lean#L268-L287

import Definitions.Def_Paper_RoundingAveraging
import Definitions.Def_Paper_RoundingDegeneracy
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset MeasureTheory
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.twoTerminal_degeneracy_rounding (H : Hypergraph) {A B : Finset ℕ} {x : ℕ → ℝ}
    (hA : A ⊆ H.vertices) (hB : B ⊆ H.vertices) (hx : H.FractionalSeparator A B x) :
    ∃ S ⊆ H.vertices.filter (fun v => x v ≠ 0), H.IntegralSeparator A B S ∧
      H.setCoverCost S ≤ (6 * H.degeneracy : ℝ) * H.coverCost x := by sorry
