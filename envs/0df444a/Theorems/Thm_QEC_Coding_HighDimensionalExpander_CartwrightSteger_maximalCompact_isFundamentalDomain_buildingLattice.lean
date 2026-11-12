-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_maximalCompact_isFundamentalDomain_buildingLattice
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.maximalCompact_isFundamentalDomain_buildingLattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:50:53.176397+00:00
-- url     : https://prove2.me/theorems/c2726f70-7508-40c0-b422-9639ea6e3b45
-- title:
--   Cartwright Steger: maximal Compact is Fundamental Domain building Lattice
-- statement:
--   Exact maximal-compact fundamental domain for the full locally embedded
--   Cartwright--Steger lattice.  Existence is the proved vertex transitivity;
--   uniqueness is the proved trivial stabilizer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/QuotientL2.lean#L106-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/QuotientL2.lean#L106-L115

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalRepresentation
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
import Mathlib.MeasureTheory.Measure.Haar.Quotient
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.GroupTheory.FreeGroup.Basic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_QuotientL2
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open MeasureTheory Set
open scoped ENNReal SphericalHecke.LocalTopology MatrixGroups Pointwise
open QEC.Coding.HighDimensionalExpander.SphericalHecke

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.maximalCompact_isFundamentalDomain_buildingLattice
    (P : BasePrime) (r : Rank) :
    IsFundamentalDomain
      (BuildingCartwrightStegerLattice P r)
      (maximalCompact (BaseField P) r.matrixRank :
        Set (HeckeGroup (BaseField P) r.matrixRank))
      (normalizedLocalHaarMeasure (BaseField P) r.matrixRank) := by sorry
