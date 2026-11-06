-- Prove2me | Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_tsupport_grad_subset
-- name    : RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.tsupport_grad_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:37:54.643197+00:00
-- url     : https://prove2.me/theorems/5abb8483-ee9a-4639-93d1-c28d45148285
-- title:
--   Euclidean: tsupport grad subset
-- statement:
--   The Euclidean construction uses the tsupport grad subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L106-L113
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L106-L113

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Topology.Algebra.Support
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_H1
set_option autoImplicit true
open RellichKondrachov
open RellichKondrachov.Analysis
open RellichKondrachov.Analysis.FunctionalSpaces
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
open scoped ENNReal MeasureTheory
open MeasureTheory
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpaceH1
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instBorelSpaceH1
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instOpensMeasurableSpaceH1
variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ]

theorem RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.tsupport_grad_subset (f : E → ℝ) : tsupport (grad (E := E) f) ⊆ tsupport f := by sorry
