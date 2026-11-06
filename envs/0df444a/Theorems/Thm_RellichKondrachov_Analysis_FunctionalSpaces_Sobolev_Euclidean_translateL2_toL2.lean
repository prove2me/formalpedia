-- Prove2me | Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_translateL2_toL2
-- name    : RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.translateL2_toL2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:37:59.423141+00:00
-- url     : https://prove2.me/theorems/5ee9cf0d-5124-48b5-ba53-bbe1d7fe92c4
-- title:
--   Euclidean: translate L2 to L2
-- statement:
--   The Euclidean construction uses the translate L2 to L2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L118-L140
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L118-L140

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_H1
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_Translation
set_option autoImplicit true
open RellichKondrachov
open RellichKondrachov.Analysis
open RellichKondrachov.Analysis.FunctionalSpaces
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
open scoped ENNReal MeasureTheory Topology
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpaceTranslation
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instBorelSpaceTranslation
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instOpensMeasurableSpaceTranslation
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableAddTranslation
variable (μ : Measure E) [μ.IsAddRightInvariant]
variable [IsFiniteMeasureOnCompacts μ]
omit [CompleteSpace E]

theorem RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.translateL2_toL2 (a : E) (f : ↥(C1c (E := E))) :
    translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) =
      toL2 (μ := μ) (E := E) (translateC1c (E := E) a f) := by sorry
