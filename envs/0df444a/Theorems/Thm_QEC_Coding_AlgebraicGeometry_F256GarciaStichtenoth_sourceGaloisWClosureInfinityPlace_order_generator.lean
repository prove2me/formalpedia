-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWClosureInfinityPlace_order_generator
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureInfinityPlace_order_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:31:46.711657+00:00
-- url     : https://prove2.me/theorems/1fd6fed7-4b9d-468c-822c-ffd0436ad1de
-- title:
--   F256 Garcia Stichtenoth: source Galois WClosure Infinity Place order generator
-- statement:
--   The embedded `w` has a normalized simple pole at the transported infinity
--   place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWClosurePlaces.lean#L77-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWClosurePlaces.lean#L77-L82

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWClosurePlaces
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureInfinityPlace_order_generator (m : ℕ) :
    (sourceGaloisWClosureInfinityPlace m).order (sourceGaloisWClosureGenerator m) = -1 := by sorry
