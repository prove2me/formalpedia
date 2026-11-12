-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_isUnitary_of_occursInLSVAutomorphicL2
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.isUnitary_of_occursInLSVAutomorphicL2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:07:01.359217+00:00
-- url     : https://prove2.me/theorems/e3e57e4d-300c-4712-a5df-0100524becff
-- title:
--   Cartwright Steger: is Unitary of occurs In LSVAutomorphic L2
-- statement:
--   Closed isometric occurrence in the concrete quotient `L²` forces
--   unitarity.  Thus unitarity is inherited from the proved right-regular
--   representation and is not independent caller-supplied representation data.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/RamanujanCriterion.lean#L65-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/RamanujanCriterion.lean#L65-L98

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_PrefixHeckeCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_QuotientL2
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_RamanujanCriterion
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open QEC.Coding.HighDimensionalExpander.SphericalHecke
universe u

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.isUnitary_of_occursInLSVAutomorphicL2
    (P : BasePrime) (r : Rank) (level : Nat)
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (sigma : Representation ℂ
      (HeckeGroup (BaseField P) r.matrixRank) V)
    (hoccurs : OccursInLSVAutomorphicL2 P r level sigma) :
    IsUnitary sigma := by sorry
