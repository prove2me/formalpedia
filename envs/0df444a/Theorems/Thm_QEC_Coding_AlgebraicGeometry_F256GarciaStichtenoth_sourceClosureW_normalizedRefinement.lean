-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureW_normalizedRefinement
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureW_normalizedRefinement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:44:37.832622+00:00
-- url     : https://prove2.me/theorems/51817212-bea6-48b4-b08d-a9a9f13922f9
-- title:
--   F256 Garcia Stichtenoth: source Closure W normalized Refinement
-- statement:
--   The source's full F9 normalized chain, on the actual finite normal
--   closure and at an arbitrary final place. It begins at the common `k(w)`,
--   includes the whole original source chain and all its conjugates, and ends
--   at the complete constructed closure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureRefinement.lean#L36-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureRefinement.lean#L36-L71

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureConjugateChains
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureRefinement
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] sourceConstantBaseTower

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureW_normalizedRefinement (m : ℕ)
    (Q : GlobalPlace F256 (SourceGaloisClosureField m)) :
    PlaceNormalizedRefinement (sourceClosureWBase m) Q ⊥ ⊤ := by sorry
