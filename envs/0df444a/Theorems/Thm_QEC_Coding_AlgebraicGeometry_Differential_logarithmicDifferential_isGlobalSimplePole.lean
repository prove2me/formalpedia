-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_logarithmicDifferential_isGlobalSimplePole
-- name    : QEC.Coding.AlgebraicGeometry.Differential.logarithmicDifferential_isGlobalSimplePole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:36:10.751585+00:00
-- url     : https://prove2.me/theorems/f3ade950-e032-469c-bbd6-f9c0080519e0
-- title:
--   Differential: logarithmic Differential is Global Simple Pole
-- statement:
--   Every nonzero function's logarithmic differential has at most a simple
--   pole at every global place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/LogarithmicResidue.lean#L145-L150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/LogarithmicResidue.lean#L145-L150

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
open QEC.Coding.AlgebraicGeometry.Differential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]

theorem QEC.Coding.AlgebraicGeometry.Differential.logarithmicDifferential_isGlobalSimplePole (f : F) (hf : f ≠ 0) :
    IsGlobalSimplePole (k := k) (F := F)
      (logarithmicDifferential (k := k) (F := F) f) := by sorry
