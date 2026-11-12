-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_lsvRightRegularRepresentation_ae_eq
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvRightRegularRepresentation_ae_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:52:16.756067+00:00
-- url     : https://prove2.me/theorems/1e05822b-eae6-4d82-b94c-be5c1e86903b
-- title:
--   Cartwright Steger: lsv Right Regular Representation ae eq
-- statement:
--   Pointwise almost-everywhere formula for the right-regular action in the
--   standard right-coset model.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/QuotientL2.lean#L574-L582
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/QuotientL2.lean#L574-L582

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvRightRegularRepresentation_ae_eq
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : HeckeGroup (BaseField P) r.matrixRank)
    (f : LSVAutomorphicL2 P r level) :
    lsvRightRegularRepresentation P r level g f =ᵐ[
        lsvAutomorphicQuotientMeasure P r level]
      (fun q ↦ f (g⁻¹ • q)) := by sorry
