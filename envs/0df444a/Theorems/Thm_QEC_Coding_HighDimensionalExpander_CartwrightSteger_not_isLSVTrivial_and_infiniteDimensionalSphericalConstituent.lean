-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_not_isLSVTrivial_and_infiniteDimensionalSphericalConstituent
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.not_isLSVTrivial_and_infiniteDimensionalSphericalConstituent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:54:10.193636+00:00
-- url     : https://prove2.me/theorems/ad9f4f6a-ca5e-4d5f-ab58-5d23b39ecbb1
-- title:
--   Cartwright Steger: not is LSVTrivial and infinite Dimensional Spherical Constituent
-- statement:
--   The representation-theoretic trivial and infinite-dimensional sectors
--   are disjoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/RamanujanCriterion.lean#L131-L139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/RamanujanCriterion.lean#L131-L139

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_PrefixHeckeCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_QuotientL2
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_RamanujanCriterion
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open QEC.Coding.HighDimensionalExpander.SphericalHecke
universe u

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.not_isLSVTrivial_and_infiniteDimensionalSphericalConstituent
    (P : BasePrime) (r : Rank) (level : Nat)
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (sigma : Representation ℂ
      (HeckeGroup (BaseField P) r.matrixRank) V) :
    ¬ (IsLSVTrivialSphericalConstituent P r level sigma ∧
      IsLSVInfiniteDimensionalSphericalConstituent P r level sigma) := by sorry
