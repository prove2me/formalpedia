-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_differentialOrder_smul
-- name    : QEC.Coding.AlgebraicGeometry.Differential.differentialOrder_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:33:14.186337+00:00
-- url     : https://prove2.me/theorems/3e424365-0107-4921-b792-5cb435ec1d8f
-- title:
--   Differential: differential Order smul
-- statement:
--   Scaling a nonzero differential by a nonzero function adds their local
--   orders.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/ResidueProduct.lean#L36-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/ResidueProduct.lean#L36-L47

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_Residue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.Differential.differentialOrder_smul (P : GlobalPlace k F) (f : F) (hf : f ≠ 0)
    (omega : Differential k F) (homega : omega ≠ 0) :
    differentialOrder (k := k) (F := F) P (f • omega)
        (smul_ne_zero hf homega) =
      P.order f + differentialOrder (k := k) (F := F) P omega homega := by sorry
