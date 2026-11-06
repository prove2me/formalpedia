-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidue_logarithmicDifferential_apply
-- name    : QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidue_logarithmicDifferential_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:39:18.151193+00:00
-- url     : https://prove2.me/theorems/64acf835-aee4-4f84-bdcb-6a538301ebc3
-- title:
--   Differential: global Simple Pole Residue logarithmic Differential apply
-- statement:
--   A coefficient of the finite global residue family of `df / f` is the
--   place order weighted by the place residue degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Global/LogarithmicResidue.lean#L72-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Global/LogarithmicResidue.lean#L72-L81

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

theorem QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidue_logarithmicDifferential_apply
    (f : F) (hf : f ≠ 0) (P : GlobalPlace k F) :
    globalSimplePoleResidue (k := k) (F := F)
        (logarithmicDifferential (k := k) (F := F) f)
        (logarithmicDifferential_isGlobalSimplePole
          (k := k) (F := F) f hf) P =
      (GlobalPlace.residueDegree (k := k) (F := F) P : k) * (P.order f : k) := by sorry
