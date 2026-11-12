-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_isLSVSphericalConstituent_of_occurs
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.isLSVSphericalConstituent_of_occurs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:52:15.596393+00:00
-- url     : https://prove2.me/theorems/a2a89e65-e528-4274-a592-885e3d6cecef
-- title:
--   Cartwright Steger: is LSVSpherical Constituent of occurs
-- statement:
--   Every actual irreducible spherical occurrence may use the inherited
--   unitarity theorem when discharging the constituent predicate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/RamanujanCriterion.lean#L102-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/RamanujanCriterion.lean#L102-L113

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_PrefixHeckeCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_QuotientL2
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_RamanujanCriterion
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open QEC.Coding.HighDimensionalExpander.SphericalHecke
universe u

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.isLSVSphericalConstituent_of_occurs
    (P : BasePrime) (r : Rank) (level : Nat)
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (sigma : Representation ℂ
      (HeckeGroup (BaseField P) r.matrixRank) V)
    (hoccurs : OccursInLSVAutomorphicL2 P r level sigma)
    (hirreducible : Representation.IsIrreducible sigma)
    (hspherical : IsSpherical sigma) :
    IsLSVSphericalConstituent P r level sigma := by sorry
