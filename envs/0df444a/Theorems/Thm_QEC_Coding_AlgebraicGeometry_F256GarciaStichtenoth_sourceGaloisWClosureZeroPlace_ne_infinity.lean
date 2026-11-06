-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWClosureZeroPlace_ne_infinity
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureZeroPlace_ne_infinity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:35:24.507222+00:00
-- url     : https://prove2.me/theorems/a4b5f055-e775-4049-8888-31c64680d7b3
-- title:
--   F256 Garcia Stichtenoth: source Galois WClosure Zero Place ne infinity
-- statement:
--   The transported zero and infinity places remain distinct.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWClosurePlaces.lean#L85-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWClosurePlaces.lean#L85-L96

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWClosurePlaces
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureZeroPlace_ne_infinity (m : ℕ) :
    sourceGaloisWClosureZeroPlace m ≠ sourceGaloisWClosureInfinityPlace m := by sorry
