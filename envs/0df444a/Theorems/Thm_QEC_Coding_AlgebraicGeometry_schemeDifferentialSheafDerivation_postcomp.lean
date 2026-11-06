-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialSheafDerivation_postcomp
-- name    : QEC.Coding.AlgebraicGeometry.schemeDifferentialSheafDerivation_postcomp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:54:03.043234+00:00
-- url     : https://prove2.me/theorems/3d3f78b1-cdc0-450a-baa5-3150dd53dcf2
-- title:
--   Algebraic Geometry: scheme Differential Sheaf Derivation postcomp
-- statement:
--   The Algebraic Geometry construction uses the scheme Differential Sheaf Derivation postcomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeDifferentials.lean#L96-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeDifferentials.lean#L96-L101

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
variable (X : Scheme.{u}) (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤))
local notation "Omega" => schemeDifferentialSheaf X k c
local notation "constants" => schemeConstantPresheafMap X k c

theorem QEC.Coding.AlgebraicGeometry.schemeDifferentialSheafDerivation_postcomp (M : X.Modules) (f : Omega ⟶ M) :
    (schemeDifferentialSheafDerivation X k c).postcomp
      ((Scheme.Modules.toPresheafOfModules X).map f) =
    schemeDifferentialSheafHomEquiv X k c M f := by sorry
