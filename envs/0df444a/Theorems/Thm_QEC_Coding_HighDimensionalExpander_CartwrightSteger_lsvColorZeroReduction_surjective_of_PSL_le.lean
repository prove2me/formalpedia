-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_lsvColorZeroReduction_surjective_of_PSL_le
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvColorZeroReduction_surjective_of_PSL_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:01:40.865977+00:00
-- url     : https://prove2.me/theorems/46ae10a4-c9b4-4312-b693-a9f075a9cd28
-- title:
--   Cartwright Steger: lsv Color Zero Reduction surjective of PSL le
-- statement:
--   Under the concrete finite `PSL` containment, every determinant-zero
--   finite image element lifts to a lattice element of building color zero.
--   Perfectness of the already constructed finite `PSL` supplies the reverse
--   lifting: commutators lift through the surjective congruence reduction and
--   every commutator has zero color.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L273-L314
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L273-L314

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped BigOperators
open QEC.Coding.HighDimensionalExpander.SphericalHecke

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvColorZeroReduction_surjective_of_PSL_le
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPSL : PSL P r level ≤ IndexCartwrightStegerImage P r level) :
    ∀ x : IndexCartwrightStegerColorZero P r level,
      ∃ g : (lsvBuildingLatticeColor P r).ker,
        buildingLatticeReduction P r level g.1 = x.1 := by sorry
