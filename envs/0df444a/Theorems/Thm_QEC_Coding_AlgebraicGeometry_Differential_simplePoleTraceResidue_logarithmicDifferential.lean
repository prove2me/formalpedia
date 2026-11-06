-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleTraceResidue_logarithmicDifferential
-- name    : QEC.Coding.AlgebraicGeometry.Differential.simplePoleTraceResidue_logarithmicDifferential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:39:07.806547+00:00
-- url     : https://prove2.me/theorems/5adcd124-ce7e-4194-97dc-f4259885d2c5
-- title:
--   Differential: simple Pole Trace Residue logarithmic Differential
-- statement:
--   The traced local residue of `df / f` is the valuation order weighted by
--   the degree of the actual place residue field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Global/LogarithmicResidue.lean#L38-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Global/LogarithmicResidue.lean#L38-L68

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_GlobalPrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_LogarithmicResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_logarithmicDifferential_isGlobalSimplePole

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.Differential.simplePoleTraceResidue_logarithmicDifferential
    (P : GlobalPlace k F) (f : F) (hf : f ≠ 0) :
    simplePoleTraceResidue (k := k) (F := F) P
        (logarithmicDifferential (k := k) (F := F) f)
        (logarithmicDifferential_isGlobalSimplePole
          (k := k) (F := F) f hf P) =
      (GlobalPlace.residueDegree (k := k) (F := F) P : k) * (P.order f : k) := by sorry
