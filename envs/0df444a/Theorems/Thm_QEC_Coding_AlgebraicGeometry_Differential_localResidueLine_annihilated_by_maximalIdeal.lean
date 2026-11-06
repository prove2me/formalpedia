-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_localResidueLine_annihilated_by_maximalIdeal
-- name    : QEC.Coding.AlgebraicGeometry.Differential.localResidueLine_annihilated_by_maximalIdeal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:15:30.884835+00:00
-- url     : https://prove2.me/theorems/36c557ad-0eb6-47dc-ae5b-718d49e501b2
-- title:
--   Differential: local Residue Line annihilated by maximal Ideal
-- statement:
--   The maximal ideal kills the simple-pole quotient modulo regular
--   differentials.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialLocal.lean#L265-L290
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialLocal.lean#L265-L290

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

theorem QEC.Coding.AlgebraicGeometry.Differential.localResidueLine_annihilated_by_maximalIdeal (P : GlobalPlace k F) :
    Module.IsTorsionBySet P.valuationRing (localResidueLine P)
      (IsLocalRing.maximalIdeal P.valuationRing) := by sorry
