-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_lsvCongruenceBuildingColorImage_eq_residueKernel_of_PSL_le
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvCongruenceBuildingColorImage_eq_residueKernel_of_PSL_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:43:06.124013+00:00
-- url     : https://prove2.me/theorems/25cc005c-4089-46ff-9239-bf5a42aee750
-- title:
--   Cartwright Steger: lsv Congruence Building Color Image eq residue Kernel of PSL le
-- statement:
--   Exact bidirectional building-color descent under the concrete `PSL`
--   containment: the colors realized by the congruence subgroup are precisely the
--   kernel of the quotient from `Z/dZ` to the finite residue determinant class.
--   This is the group-level content behind LSV05a's `ζ^(d/t) = 1` condition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L327-L362
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L327-L362

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped BigOperators
open QEC.Coding.HighDimensionalExpander.SphericalHecke

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvCongruenceBuildingColorImage_eq_residueKernel_of_PSL_le
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPSL : PSL P r level ≤ IndexCartwrightStegerImage P r level) :
    lsvCongruenceBuildingColorImage P r level =
      (lsvBuildingColorToResidueDetClass P r level).ker := by sorry
