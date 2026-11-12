-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_lsvRightRegularRepresentation_isUnitary
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvRightRegularRepresentation_isUnitary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:03:40.227921+00:00
-- url     : https://prove2.me/theorems/b493d05b-f667-428d-ae4c-51b5a104b826
-- title:
--   Cartwright Steger: lsv Right Regular Representation is Unitary
-- statement:
--   The genuine quotient representation is unitary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/QuotientL2.lean#L585-L596
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/QuotientL2.lean#L585-L596

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvRightRegularRepresentation_isUnitary
    (P : BasePrime) (r : Rank) (level : Nat) :
    SphericalHecke.IsUnitary
      (lsvRightRegularRepresentation P r level) := by sorry
