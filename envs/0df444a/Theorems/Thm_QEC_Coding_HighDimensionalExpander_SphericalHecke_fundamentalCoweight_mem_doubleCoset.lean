-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalCoweight_mem_doubleCoset
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalCoweight_mem_doubleCoset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:46:41.335899+00:00
-- url     : https://prove2.me/theorems/b0e1d597-2b02-45d9-b13d-598f076116ce
-- title:
--   Spherical Hecke: fundamental Coweight mem double Coset
-- statement:
--   The Spherical Hecke construction uses the fundamental Coweight mem double Coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHecke.lean#L528-L535
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHecke.lean#L528-L535

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalCoweight_mem_doubleCoset
    (k : Type u) [Field k] (d r : ℕ) :
    fundamentalCoweight k d r ∈ fundamentalDoubleCoset k d r := by sorry
