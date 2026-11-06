-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_differential_mem_localDifferentialLattice
-- name    : QEC.Coding.AlgebraicGeometry.Differential.differential_mem_localDifferentialLattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:17:51.828207+00:00
-- url     : https://prove2.me/theorems/943dda77-1f19-41a9-8485-faa071b754e9
-- title:
--   Differential: differential mem local Differential Lattice
-- statement:
--   A differential of a function regular at `P` lies in the constructed local
--   differential lattice.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialLocal.lean#L123-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialLocal.lean#L123-L126

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

theorem QEC.Coding.AlgebraicGeometry.Differential.differential_mem_localDifferentialLattice (P : GlobalPlace k F)
    (f : P.valuationRing) :
    differential k F (f : F) ∈ localDifferentialLattice P := by sorry
