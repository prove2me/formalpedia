-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWZeroPlace_ne_infinity
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroPlace_ne_infinity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:35:11.769809+00:00
-- url     : https://prove2.me/theorems/dec51cd6-989a-4b4e-8b63-dd0d4b63352f
-- title:
--   F256 Garcia Stichtenoth: source Galois WZero Place ne infinity
-- statement:
--   The zero and infinity places of `F256(w)` are genuinely distinct.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWPlaces.lean#L107-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWPlaces.lean#L107-L117

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWIntermediate
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_StepPlaceTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ZeroPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_RationalBaseInfinityCancellation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPlaces
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
open IntermediateField Polynomial

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroPlace_ne_infinity :
    sourceGaloisWZeroPlace ≠ sourceGaloisWInfinityPlace := by sorry
