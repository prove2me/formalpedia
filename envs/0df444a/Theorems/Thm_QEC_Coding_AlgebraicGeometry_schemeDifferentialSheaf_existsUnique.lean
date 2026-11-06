-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialSheaf_existsUnique
-- name    : QEC.Coding.AlgebraicGeometry.schemeDifferentialSheaf_existsUnique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:57:25.479413+00:00
-- url     : https://prove2.me/theorems/5e650ddf-5b11-4f96-a391-3e8f5b337a74
-- title:
--   Algebraic Geometry: scheme Differential Sheaf exists Unique
-- statement:
--   Every actual derivation into a sheaf has a unique sheaf-module factorization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeDifferentials.lean#L69-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeDifferentials.lean#L69-L79

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeDifferentials
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable (X : Scheme.{u}) (k : CommRingCat.{u})

theorem QEC.Coding.AlgebraicGeometry.schemeDifferentialSheaf_existsUnique (c : k ⟶ Γ(X, ⊤))
    (M : X.Modules)
    (d : ((Scheme.Modules.toPresheafOfModules X).obj M).Derivation'
      (schemeConstantPresheafMap X k c)) :
    ∃! f : schemeDifferentialSheaf X k c ⟶ M,
      schemeDifferentialSheafHomEquiv X k c M f = d := by sorry
