-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCongruence_color_mem_residueKernel
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCongruence_color_mem_residueKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:01:41.108775+00:00
-- url     : https://prove2.me/theorems/2019e77e-172e-4322-8cb6-6e1d13dee7a4
-- title:
--   Cartwright Steger: building Congruence color mem residue Kernel
-- statement:
--   The selected principal congruence subgroup has building color in the
--   kernel of the finite color quotient.  The reverse inclusion is proved below
--   under the concrete finite `PSL` containment.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L252-L266
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L252-L266

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped BigOperators
open QEC.Coding.HighDimensionalExpander.SphericalHecke

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCongruence_color_mem_residueKernel
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : BuildingCartwrightStegerCongruenceSubgroup P r level) :
    lsvBuildingLatticeColor P r g.1 ∈
      (lsvBuildingColorToResidueDetClass P r level).ker := by sorry
