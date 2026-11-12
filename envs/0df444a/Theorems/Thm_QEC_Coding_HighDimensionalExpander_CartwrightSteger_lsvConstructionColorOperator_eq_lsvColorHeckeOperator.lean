-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_lsvConstructionColorOperator_eq_lsvColorHeckeOperator
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvConstructionColorOperator_eq_lsvColorHeckeOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:49:21.412921+00:00
-- url     : https://prove2.me/theorems/8f1ee7f3-0746-41f6-8519-72e8988c7f62
-- title:
--   Cartwright Steger: lsv Construction Color Operator eq lsv Color Hecke Operator
-- statement:
--   The source-prefix presentation and the actual fundamental-neighbor
--   presentation are equal without collapsing multiplicity: the building lattice
--   orbit map is injective by simple transitivity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/PrefixHeckeCompatibility.lean#L709-L732
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/PrefixHeckeCompatibility.lean#L709-L732

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_PrefixHeckeCompatibility
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups Pointwise
open QEC.Coding.HighDimensionalExpander.SphericalHecke
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingVertexDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvConstructionColorOperator_eq_lsvColorHeckeOperator
    (P : BasePrime) (r : Rank) (level color : Nat)
    (hcolor : color ∈ Finset.Icc 1 (r.matrixRank - 1)) :
    lsvConstructionColorOperator P r level color =
      lsvColorHeckeOperator P r level color := by sorry
