-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityRamificationIndex_even
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWInfinityRamificationIndex_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:10:54.947869+00:00
-- url     : https://prove2.me/theorems/2197004b-4820-4d5b-b240-f262d26acc5c
-- title:
--   F256 Garcia Stichtenoth: source Galois WInfinity Ramification Index even
-- statement:
--   The common infinity-fibre ramification index is even.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWRamification.lean#L141-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWRamification.lean#L141-L145

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWGlobalPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWRamification
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWInfinityRamificationIndex_even (m : ℕ) :
    Even (sourceGaloisWInfinityRamificationIndex m) := by sorry
