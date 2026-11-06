-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWClosureGenerator_pow_fifteen
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureGenerator_pow_fifteen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:26:29.493691+00:00
-- url     : https://prove2.me/theorems/212cfd51-275d-4cc4-9503-94dd22b22e72
-- title:
--   F256 Garcia Stichtenoth: source Galois WClosure Generator pow fifteen
-- statement:
--   The embedded generator satisfies the source relation `w^15 = z`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWIntermediate.lean#L138-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWIntermediate.lean#L138-L146

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisFunctionField
import Mathlib.FieldTheory.Relrank
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWIntermediate
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
open IntermediateField Polynomial

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureGenerator_pow_fifteen (m : ℕ) :
    ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) :
        SourceGaloisClosureField m) ^ 15 =
      algebraMap GaloisBaseField (SourceGaloisClosureField m)
        (AdjoinSimple.gen F256 galoisBaseZ) := by sorry
