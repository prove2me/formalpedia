-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureConjugateW_adjoin
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureConjugateW_adjoin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:43:38.439343+00:00
-- url     : https://prove2.me/theorems/b92b62ca-dabc-43d5-8bf6-6060de11fc1f
-- title:
--   F256 Garcia Stichtenoth: source Closure Conjugate W adjoin
-- statement:
--   The initial rational parameter of each actual conjugate generates
--   exactly the common `k(w)` subfield; the conjugate need not fix `w` itself.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureConjugateChains.lean#L60-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureConjugateChains.lean#L60-L73

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureConjugateW_adjoin (m : ℕ)
    (f : SourceField m →ₐ[GaloisBaseField] SourceGaloisClosureField m) :
    F256⟮f (algebraMap (RatFunc F256) (SourceField m) galoisBaseW)⟯ = sourceClosureWBase m := by sorry
