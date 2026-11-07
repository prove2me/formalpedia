-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_specialLinear_fixed_projective_is_homothety
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.specialLinear_fixed_projective_is_homothety
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:43:41.44236+00:00
-- url     : https://prove2.me/theorems/deb620e7-4403-4127-af0f-294f09bc16b5
-- title:
--   Cartwright Steger: special Linear fixed projective is homothety
-- statement:
--   A special-linear map fixing every projective point is a homothety.  This
--   is the kernel calculation needed below; it is proved from collinearity of
--   every vector with its image, not assumed as faithfulness of projective
--   action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/SpecialLinear.lean#L461-L484
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/SpecialLinear.lean#L461-L484

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.GroupTheory.GroupAction.Iwasawa
import Mathlib.GroupTheory.IsPerfect
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Independence
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_SpecialLinear
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Matrix
open scoped commutatorElement
open scoped Pointwise
open scoped LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.specialLinear_fixed_projective_is_homothety
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Free K V]
    (a : SpecialLinearGroup K V)
    (hfix : ∀ x : ℙ K V, a • x = x) :
    ∃ c : K, (a : V ≃ₗ[K] V).toLinearMap = c • 1 := by sorry
