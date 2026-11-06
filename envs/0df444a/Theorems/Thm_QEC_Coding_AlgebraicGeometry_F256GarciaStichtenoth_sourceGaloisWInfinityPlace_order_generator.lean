-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityPlace_order_generator
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWInfinityPlace_order_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:29:50.08905+00:00
-- url     : https://prove2.me/theorems/e1ba04e1-ae39-4c25-943a-0197f20c340f
-- title:
--   F256 Garcia Stichtenoth: source Galois WInfinity Place order generator
-- statement:
--   The generator `w` has a normalized simple pole at the transported
--   infinity place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWPlaces.lean#L97-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWPlaces.lean#L97-L104

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWIntermediate
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_StepPlaceTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ZeroPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_RationalBaseInfinityCancellation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPlaces
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
open IntermediateField Polynomial

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWInfinityPlace_order_generator :
    sourceGaloisWInfinityPlace.order sourceGaloisWFieldGenerator = -1 := by sorry
