-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_lsvCongruenceFundamentalDomain_isFundamentalDomain_local
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvCongruenceFundamentalDomain_isFundamentalDomain_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:50:52.343982+00:00
-- url     : https://prove2.me/theorems/1555c6c8-a674-49a0-bbbf-bc8a84c46673
-- title:
--   Cartwright Steger: lsv Congruence Fundamental Domain is Fundamental Domain local
-- statement:
--   The same explicit finite union is a fundamental domain for the literal
--   local subgroup used in the quotient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/QuotientL2.lean#L350-L358
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/QuotientL2.lean#L350-L358

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvCongruenceFundamentalDomain_isFundamentalDomain_local
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsFundamentalDomain
      (lsvLocalCongruenceSubgroup P r level)
      (lsvCongruenceFundamentalDomain P r level)
      (normalizedLocalHaarMeasure (BaseField P) r.matrixRank) := by sorry
