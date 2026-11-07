-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projective_mk_mem_maximalCompact_iff_integral
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.projective_mk_mem_maximalCompact_iff_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:50:52.400305+00:00
-- url     : https://prove2.me/theorems/da706d03-ca6c-4922-bf13-23f12b0096fc
-- title:
--   Spherical Hecke: projective mk mem maximal Compact iff integral
-- statement:
--   For positive matrix rank and determinant order zero, projective maximal
--   compactness is equivalent to honest integrality of the matrix and its inverse.
--   The determinant hypothesis removes the otherwise invisible projective scalar.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L126-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L126-L162

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.projective_mk_mem_maximalCompact_iff_integral
    (k : Type*) [Field k] [Finite k] (d : ℕ) (hd : 0 < d)
    (A : GL (Fin d) (LocalFunctionField k))
    (hdet : localUnitOrder (Matrix.GeneralLinearGroup.det A) = 0) :
    Matrix.ProjGenLinGroup.mk A ∈ maximalCompact k d ↔
      A ∈ integralGeneralLinearSet k d := by sorry
