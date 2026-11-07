-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThree_buildingDimension
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThree_buildingDimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:03:32.044512+00:00
-- url     : https://prove2.me/theorems/72f84176-7e1e-4334-8a4e-0803a60c21d0
-- title:
--   Spherical Hecke: rank Three building Dimension
-- statement:
--   Matrix rank three corresponds to building dimension two.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHecke.lean#L633-L634
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHecke.lean#L633-L634

import Mathlib.Algebra.Group.Pi.Units
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups Pointwise
universe u
open scoped LocalTopology
open MeasureTheory

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThree_buildingDimension : 3 - 1 = 2 := by sorry
