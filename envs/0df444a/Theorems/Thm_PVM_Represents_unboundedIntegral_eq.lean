-- Prove2me | Theorems.Thm_PVM_Represents_unboundedIntegral_eq
-- name    : PVM.Represents.unboundedIntegral_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:12:15.079144+00:00
-- url     : https://prove2.me/theorems/810ea755-0f5f-4c0c-a772-653782e23592
-- title:
--   Represents: unbounded Integral eq
-- statement:
--   The intrinsic representation is equivalent to the library's spectral
--   integral representation. In particular, its diagonal moment formulation does
--   not weaken the operator equality: complex polarization recovers every mixed
--   matrix coefficient.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Intrinsic.lean#L65-L140
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Intrinsic.lean#L65-L140

import Definitions.Def_Spectral_Spectral_Uniqueness
import Definitions.Def_Spectral_Spectral_Intrinsic
set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem PVM.Represents.unboundedIntegral_eq
    {E_pvm : PVM E} {A : E →ₗ.[ℂ] E} (hrep : E_pvm.Represents A)
    (hA : IsSelfAdjoint A) :
    E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable = A := by sorry
