-- Prove2me | Theorems.Thm_P2M_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_uniformContinuous___cf87d892dee5
-- name    : P2M_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_uniformContinuous___cf87d892dee5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:52:43.4787+00:00
-- url     : https://prove2.me/theorems/62b1384e-68b9-4d68-a8de-9ec62c6005f6
-- title:
--   P2 M Rellich Kondrachov Analysis Functional Spaces Sobolev Euclidean L2 Compactness uniform Continuous   cf87d892dee5: P2 M Rellich Kondrachov Analysis Functional Spaces Sobolev Euclidean L2 Compactne
-- statement:
--   The P2 M Rellich Kondrachov Analysis Functional Spaces Sobolev Euclidean L2 Compactness uniform Continuous   cf87d892dee5 construction uses the P2 M Rellich Kondrachov Analysis Functional Spaces Sobolev Euclidean L2 Compactness uniform Continuous   cf87d892dee5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L97-L123
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L97-L123

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Smoothing
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Compactness
set_option autoImplicit true
open RellichKondrachov
open RellichKondrachov.Analysis
open RellichKondrachov.Analysis.FunctionalSpaces
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness
open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableSpaceEL2CompactnessCompactness
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instBorelSpaceEL2CompactnessCompactness
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instOpensMeasurableSpaceEL2CompactnessCompactness
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableAddEL2CompactnessCompactness
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableNegEL2CompactnessCompactness
variable {K : Set E}
variable {ψ : E → ℝ}
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem P2M_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_uniformContinuous___cf87d892dee5 (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) :
    UniformContinuous ψ := by sorry

alias «RellichKondrachov».«Analysis».«FunctionalSpaces».«Sobolev».«Euclidean».«L2Compactness».«uniformContinuous_ψ» := P2M_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_uniformContinuous___cf87d892dee5
