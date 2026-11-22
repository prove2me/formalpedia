-- Prove2me | Theorems.Thm_Paper_Hypergraph_levelSeparator_integral
-- name    : Paper.Hypergraph.levelSeparator_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:37.758499+00:00
-- url     : https://prove2.me/theorems/e45180d0-9698-4fbb-9791-af1dc42035f1
-- title:
--   Hypergraph: level Separator integral
-- statement:
--   Observation 4.4 for interior levels, which suffice for averaging.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/TwoTerminalRounding.lean#L139-L187
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/TwoTerminalRounding.lean#L139-L187

import Definitions.Def_Paper_RoundingSeparation
import Definitions.Def_Paper_TwoTerminalRounding
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.levelSeparator_integral (H : Hypergraph) {A B : Finset ℕ} {x d : ℕ → ℝ}
    (hA : A ⊆ H.vertices) (hB : B ⊆ H.vertices)
    (ha : ∀ v ∈ A, d v ≤ x v) (hb : ∀ v ∈ B, 1 ≤ d v)
    (hstep : ∀ u ∈ H.vertices, ∀ v ∈ H.vertices, H.primal.Adj u v → d v ≤ d u + x v)
    {r : ℝ} (hr : 0 < r ∧ r < 1) : H.IntegralSeparator A B (H.levelSeparator x d r) := by sorry
