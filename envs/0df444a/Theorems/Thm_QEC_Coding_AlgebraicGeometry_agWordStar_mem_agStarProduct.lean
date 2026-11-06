-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_agWordStar_mem_agStarProduct
-- name    : QEC.Coding.AlgebraicGeometry.agWordStar_mem_agStarProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:26:29.74142+00:00
-- url     : https://prove2.me/theorems/dbf2f634-f12e-480f-9020-9f1dcbf925ff
-- title:
--   Algebraic Geometry: ag Word Star mem ag Star Product
-- statement:
--   A componentwise product of two codewords is a generator of their actual
--   star-product submodule.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Code.lean#L48-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Code.lean#L48-L51

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Evaluation
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Code
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithZero
variable {k F ι : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
variable [Fintype ι]

theorem QEC.Coding.AlgebraicGeometry.agWordStar_mem_agStarProduct [Fintype k] (C D : LinearCode k ι)
    {x y : Word k ι} (hx : x ∈ C.carrier) (hy : y ∈ D.carrier) :
    agWordStar x y ∈ agStarProduct C D := by sorry
