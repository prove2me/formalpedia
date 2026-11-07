-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalIntegralConjugate_det_localUnitOrder_eq_zero
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalIntegralConjugate_det_localUnitOrder_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:51:25.030717+00:00
-- url     : https://prove2.me/theorems/4058d3c3-c7de-441a-bd00-47b444c4f774
-- title:
--   Spherical Hecke: fundamental Integral Conjugate det local Unit Order eq zero
-- statement:
--   Fundamental diagonal conjugation preserves determinant order zero for
--   integral invertible matrices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L375-L382
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L375-L382

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalIntegralConjugate_det_localUnitOrder_eq_zero
    (k : Type*) [Field k] (d r : ℕ)
    (g : GL (Fin d) (IntegerRing k)) :
    localUnitOrder (Matrix.GeneralLinearGroup.det
      (fundamentalIntegralConjugate k d r g)) = 0 := by sorry
