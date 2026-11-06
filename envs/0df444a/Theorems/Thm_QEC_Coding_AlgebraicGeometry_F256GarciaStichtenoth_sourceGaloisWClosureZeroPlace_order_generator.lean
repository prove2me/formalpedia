-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWClosureZeroPlace_order_generator
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureZeroPlace_order_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:33:38.641193+00:00
-- url     : https://prove2.me/theorems/2d2c7b92-4dba-4278-95c2-d05384c5a364
-- title:
--   F256 Garcia Stichtenoth: source Galois WClosure Zero Place order generator
-- statement:
--   The embedded `w` has a normalized simple zero at the transported zero
--   place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWClosurePlaces.lean#L68-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWClosurePlaces.lean#L68-L73

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWClosurePlaces
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureZeroPlace_order_generator (m : ℕ) :
    (sourceGaloisWClosureZeroPlace m).order (sourceGaloisWClosureGenerator m) = 1 := by sorry
