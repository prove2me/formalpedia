-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_isLSVTrivial_or_infiniteDimensionalSphericalConstituent
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.isLSVTrivial_or_infiniteDimensionalSphericalConstituent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:53:53.311585+00:00
-- url     : https://prove2.me/theorems/5eac0dda-7f19-4173-a112-5f3dac69f285
-- title:
--   Cartwright Steger: is LSVTrivial or infinite Dimensional Spherical Constituent
-- statement:
--   Finite-dimensional and infinite-dimensional spherical constituents form
--   an exhaustive partition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/RamanujanCriterion.lean#L117-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/RamanujanCriterion.lean#L117-L127

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_PrefixHeckeCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_QuotientL2
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_RamanujanCriterion
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open QEC.Coding.HighDimensionalExpander.SphericalHecke
universe u

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.isLSVTrivial_or_infiniteDimensionalSphericalConstituent
    (P : BasePrime) (r : Rank) (level : Nat)
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (sigma : Representation ℂ
      (HeckeGroup (BaseField P) r.matrixRank) V)
    (hconstituent : IsLSVSphericalConstituent P r level sigma) :
    IsLSVTrivialSphericalConstituent P r level sigma ∨
      IsLSVInfiniteDimensionalSphericalConstituent P r level sigma := by sorry
