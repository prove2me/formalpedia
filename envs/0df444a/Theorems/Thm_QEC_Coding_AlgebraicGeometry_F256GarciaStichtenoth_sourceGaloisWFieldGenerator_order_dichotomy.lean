-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWFieldGenerator_order_dichotomy
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWFieldGenerator_order_dichotomy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:33:16.058508+00:00
-- url     : https://prove2.me/theorems/519fb061-dad9-4533-91ee-75b4d9cfe8cb
-- title:
--   F256 Garcia Stichtenoth: source Galois WField Generator order dichotomy
-- statement:
--   The actual rational `w` generator is regular or has a simple pole at
--   every place, not only at the named infinity place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalTraceSeed.lean#L27-L33
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalTraceSeed.lean#L27-L33

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalTraceSeed
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWFieldGenerator_order_dichotomy
    (P : GlobalPlace F256 SourceGaloisWField) :
    P.order sourceGaloisWFieldGenerator = -1 ∨
      0 ≤ P.order sourceGaloisWFieldGenerator := by sorry
