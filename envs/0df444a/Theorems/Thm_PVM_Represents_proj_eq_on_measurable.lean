-- Prove2me | Theorems.Thm_PVM_Represents_proj_eq_on_measurable
-- name    : PVM.Represents.proj_eq_on_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:11:34.583509+00:00
-- url     : https://prove2.me/theorems/82a8792e-0485-5247-a2c6-7c77197e44dd
-- title:
--   Represents: proj eq on measurable
-- statement:
--   Intrinsic representations of a self-adjoint operator have the same
--   spectral projections on every measurable set.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Intrinsic.lean#L154-L160
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Intrinsic.lean#L154-L160

import Definitions.Def_Spectral_Spectral_Uniqueness
import Definitions.Def_Spectral_Spectral_Intrinsic
set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem PVM.Represents.proj_eq_on_measurable
    {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {E₁ E₂ : PVM E} (h₁ : E₁.Represents A) (h₂ : E₂.Represents A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    E₁.proj S = E₂.proj S := by sorry
