-- Prove2me | Theorems.Thm_Paper_Hypergraph_intervalMultiplier_tail
-- name    : Paper.Hypergraph.intervalMultiplier_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:59.201089+00:00
-- url     : https://prove2.me/theorems/f8413ecb-eba6-4061-b410-e800f06f5691
-- title:
--   Hypergraph: interval Multiplier tail
-- statement:
--   All intervals on one edge contain a common point, so their short members
--   lie in an interval of length at most twice their maximum length.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingAveraging.lean#L111-L136
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingAveraging.lean#L111-L136

import Definitions.Def_Paper_TwoTerminalRounding
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Paper_RoundingAveraging
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open MeasureTheory Set
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.intervalMultiplier_tail {V : Finset ℕ} (hne : V.Nonempty) {x d : ℕ → ℝ} {q : ℝ}
    (hq : ∀ v ∈ V, d v - x v ≤ q ∧ q ≤ d v) {t : ℝ} (ht : 0 < t) :
    levelMeasure.real {r | t ≤ intervalMultiplier V hne x d r} ≤ 2 / t := by sorry
