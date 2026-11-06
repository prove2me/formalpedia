-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_placeDivisor_degree
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.placeDivisor_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:34:19.335182+00:00
-- url     : https://prove2.me/theorems/2e9954b0-7f00-4b63-9219-f5d49de5322c
-- title:
--   Global Place: place Divisor degree
-- statement:
--   The weighted degree of the one-place divisor is the actual residue
--   degree of its supporting place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/PlaceIncrement.lean#L53-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/PlaceIncrement.lean#L53-L57

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PrincipalShift
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrement
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.placeDivisor_degree (P : GlobalPlace k F) :
    Divisor.degree (residueDegree (k := k) (F := F)) (placeDivisor P) =
      residueDegree (k := k) (F := F) P := by sorry
