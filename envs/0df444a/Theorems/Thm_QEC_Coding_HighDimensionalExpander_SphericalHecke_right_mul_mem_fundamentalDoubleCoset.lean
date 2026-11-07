-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_right_mul_mem_fundamentalDoubleCoset
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.right_mul_mem_fundamentalDoubleCoset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:28:40.372269+00:00
-- url     : https://prove2.me/theorems/7282f71d-ff14-4b39-b7e2-bef2ca8e3597
-- title:
--   Spherical Hecke: right mul mem fundamental Double Coset
-- statement:
--   The Spherical Hecke construction uses the right mul mem fundamental Double Coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHecke.lean#L562-L570
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHecke.lean#L562-L570

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.right_mul_mem_fundamentalDoubleCoset
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    {h x : PGL(Fin d, LocalFunctionField k)}
    (hh : h ∈ maximalCompact k d)
    (hx : x ∈ fundamentalDoubleCoset k d r) :
    x * h ∈ fundamentalDoubleCoset k d r := by sorry
