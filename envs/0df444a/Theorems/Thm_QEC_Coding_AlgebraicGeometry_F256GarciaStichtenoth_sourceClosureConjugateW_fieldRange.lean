-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureConjugateW_fieldRange
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureConjugateW_fieldRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:44:19.251567+00:00
-- url     : https://prove2.me/theorems/5b403fcb-c3be-44d6-b56e-96b758adbfb3
-- title:
--   F256 Garcia Stichtenoth: source Closure Conjugate W field Range
-- statement:
--   The existing conjugate-image theorem, now on the finite closure carrier
--   where the final place and different will actually be measured.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureConjugateChains.lean#L46-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureConjugateChains.lean#L46-L56

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureConjugateW_fieldRange (m : ℕ)
    (f : SourceField m →ₐ[GaloisBaseField] SourceGaloisClosureField m) :
    (f.comp (sourceGaloisWFieldToSource m)).fieldRange = SourceGaloisWClosureField m := by sorry
