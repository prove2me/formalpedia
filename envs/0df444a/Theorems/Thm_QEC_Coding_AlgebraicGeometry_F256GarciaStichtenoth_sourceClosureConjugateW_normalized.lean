-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureConjugateW_normalized
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureConjugateW_normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:43:58.648191+00:00
-- url     : https://prove2.me/theorems/6bafab2c-8cbd-4e4c-8548-6111cd28d79d
-- title:
--   F256 Garcia Stichtenoth: source Closure Conjugate W normalized
-- statement:
--   Every actual source conjugate, on the actual finite closure carrier,
--   admits the full w-rooted normalized refinement at every final place.
--   No normalized chain, different formula, or degree is assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureConjugateChains.lean#L78-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureConjugateChains.lean#L78-L100

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_EmbeddedWSeed
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWNormal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureConjugateChains
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceConstantBaseTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wConstantBaseTower

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureConjugateW_normalized (m : ℕ)
    (f : SourceField m →ₐ[GaloisBaseField] SourceGaloisClosureField m)
    (Q : GlobalPlace F256 (SourceGaloisClosureField m)) :
    PlaceNormalizedExtension Q (sourceClosureWBase m) (f.restrictScalars F256).fieldRange := by sorry
