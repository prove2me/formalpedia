-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_mul_mem_riemannRochSubmodule_add
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.mul_mem_riemannRochSubmodule_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:45:47.77811+00:00
-- url     : https://prove2.me/theorems/8d58755d-27e6-42c6-a892-a2c77e629ea6
-- title:
--   Global Place: mul mem riemann Roch Submodule add
-- statement:
--   The Global Place construction uses the mul mem riemann Roch Submodule add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Space.lean#L61-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Space.lean#L61-L64

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_ValuationBound
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Space
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped WithZero
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.mul_mem_riemannRochSubmodule_add {G H : Divisor (GlobalPlace k F)} {f g : F}
    (hf : f ∈ riemannRochSubmodule G) (hg : g ∈ riemannRochSubmodule H) :
    f * g ∈ riemannRochSubmodule (G + H) := by sorry
