-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWFieldEquivClosureField_generator
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWFieldEquivClosureField_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:32:09.27846+00:00
-- url     : https://prove2.me/theorems/462e864e-9fb0-44b9-8df2-7a02029748e5
-- title:
--   F256 Garcia Stichtenoth: source Galois WField Equiv Closure Field generator
-- statement:
--   The intermediate-field equivalence sends the literal generator to the
--   literal embedded generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWClosurePlaces.lean#L28-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWClosurePlaces.lean#L28-L32

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWClosurePlaces
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWFieldEquivClosureField_generator (m : ℕ) :
    ((sourceGaloisWFieldEquivClosureField m sourceGaloisWFieldGenerator :
        SourceGaloisWClosureField m) : SourceGaloisClosureField m) =
      (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m) := by sorry
