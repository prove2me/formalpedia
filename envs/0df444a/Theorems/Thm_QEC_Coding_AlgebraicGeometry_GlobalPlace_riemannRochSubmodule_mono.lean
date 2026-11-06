-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochSubmodule_mono
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:07:53.318368+00:00
-- url     : https://prove2.me/theorems/f096deb0-3b0f-423c-a910-c55f505a8585
-- title:
--   Global Place: riemann Roch Submodule mono
-- statement:
--   The Global Place construction uses the riemann Roch Submodule mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Space.lean#L57-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Space.lean#L57-L59

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_ValuationBound
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Space
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped WithZero
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule_mono {G H : Divisor (GlobalPlace k F)}
    (hGH : G ≤ H) : riemannRochSubmodule G ≤ riemannRochSubmodule H := by sorry
