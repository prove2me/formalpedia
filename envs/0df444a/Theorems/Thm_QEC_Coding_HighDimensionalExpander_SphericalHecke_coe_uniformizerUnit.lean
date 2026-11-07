-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:28:04.559886+00:00
-- url     : https://prove2.me/theorems/77b58751-0c7c-49f4-b29e-c57f72ae1d72
-- title:
--   Spherical Hecke: coe uniformizer Unit
-- statement:
--   The Spherical Hecke construction uses the coe uniformizer Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHecke.lean#L483-L486
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHecke.lean#L483-L486

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit (k : Type u) [Field k] :
    (uniformizerUnit k : LocalFunctionField k) =
      HahnSeries.single (1 : Int) 1 := by sorry

attribute [defeq] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
