-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_smul_mem_riemannRochSubmodule
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.smul_mem_riemannRochSubmodule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:14:18.356967+00:00
-- url     : https://prove2.me/theorems/b5757c04-0b2c-4965-bff8-22711dec7c3e
-- title:
--   Global Place: smul mem riemann Roch Submodule
-- statement:
--   The Global Place construction uses the smul mem riemann Roch Submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Space.lean#L52-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Space.lean#L52-L55

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_ValuationBound
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Space
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped WithZero
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.smul_mem_riemannRochSubmodule {G : Divisor (GlobalPlace k F)}
    (a : k) {f : F} (hf : f ∈ riemannRochSubmodule G) :
    a • f ∈ riemannRochSubmodule G := by sorry
