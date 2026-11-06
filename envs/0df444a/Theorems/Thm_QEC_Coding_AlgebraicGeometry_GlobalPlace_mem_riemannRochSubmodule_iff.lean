-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_mem_riemannRochSubmodule_iff
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_riemannRochSubmodule_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:11:54.005583+00:00
-- url     : https://prove2.me/theorems/dd9fb6fc-e19a-4f3d-81a3-6d4eda6dcdc4
-- title:
--   Global Place: mem riemann Roch Submodule iff
-- statement:
--   Membership is exactly the collection of all local valuation bounds.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Space.lean#L38-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Space.lean#L38-L41

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_ValuationBound
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Space
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped WithZero
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_riemannRochSubmodule_iff (G : Divisor (GlobalPlace k F)) (f : F) :
    f ∈ riemannRochSubmodule G ↔
      ∀ P, P.valuation f ≤ WithZero.exp (G P) := by sorry
