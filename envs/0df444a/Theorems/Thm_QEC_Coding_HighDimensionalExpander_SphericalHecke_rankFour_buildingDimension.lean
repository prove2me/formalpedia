-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFour_buildingDimension
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFour_buildingDimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:03:39.190203+00:00
-- url     : https://prove2.me/theorems/5f6a1b2f-0703-4dc7-8275-7ccb2980a02d
-- title:
--   Spherical Hecke: rank Four building Dimension
-- statement:
--   Matrix rank four corresponds to building dimension three.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHecke.lean#L637-L638
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHecke.lean#L637-L638

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFour_buildingDimension : 4 - 1 = 3 := by sorry
