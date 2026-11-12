-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_lsvColorHeckeOperator_const
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvColorHeckeOperator_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:46:14.718097+00:00
-- url     : https://prove2.me/theorems/22a75ff0-9904-43ba-8c04-260d5add5423
-- title:
--   Cartwright Steger: lsv Color Hecke Operator const
-- statement:
--   The constant vector has the actual universal-building colored degree as
--   its eigenvalue.  This fixes the unnormalized Hecke multiplicity convention.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L647-L653
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L647-L653

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped BigOperators
open QEC.Coding.HighDimensionalExpander.SphericalHecke

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvColorHeckeOperator_const
    (P : BasePrime) (r : Rank) (level k : Nat) (c : ℂ) :
    lsvColorHeckeOperator P r level k (fun _ ↦ c) =
      (SphericalHecke.coloredAdjacencyDegree
        (BaseField P) r.matrixRank k : ℂ) • (fun _ ↦ c) := by sorry
