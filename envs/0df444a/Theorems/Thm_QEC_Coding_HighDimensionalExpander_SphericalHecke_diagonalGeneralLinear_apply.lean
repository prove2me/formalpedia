-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:28:10.536919+00:00
-- url     : https://prove2.me/theorems/fc211ad8-f889-49bf-8810-37411da5eaaf
-- title:
--   Spherical Hecke: diagonal General Linear apply
-- statement:
--   The Spherical Hecke construction uses the diagonal General Linear apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHecke.lean#L502-L505
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHecke.lean#L502-L505

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply (R : Type u) [CommRing R] (d : ℕ)
    (u : Fin d → Units R) (i j : Fin d) :
    diagonalGeneralLinear R d u i j = if i = j then (u i : R) else 0 := by sorry
