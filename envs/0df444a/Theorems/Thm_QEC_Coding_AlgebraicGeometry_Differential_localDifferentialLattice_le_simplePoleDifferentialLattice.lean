-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_localDifferentialLattice_le_simplePoleDifferentialLattice
-- name    : QEC.Coding.AlgebraicGeometry.Differential.localDifferentialLattice_le_simplePoleDifferentialLattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:20:23.751767+00:00
-- url     : https://prove2.me/theorems/aecc9e65-ae96-41cd-867f-74a4e2712863
-- title:
--   Differential: local Differential Lattice le simple Pole Differential Lattice
-- statement:
--   Every regular differential is in the simple-pole differential lattice.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialLocal.lean#L244-L249
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialLocal.lean#L244-L249

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped WithZero
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
open QEC.Coding.AlgebraicGeometry.Differential

theorem QEC.Coding.AlgebraicGeometry.Differential.localDifferentialLattice_le_simplePoleDifferentialLattice
    (P : GlobalPlace k F) :
    localDifferentialLattice P ≤ simplePoleDifferentialLattice P := by sorry
