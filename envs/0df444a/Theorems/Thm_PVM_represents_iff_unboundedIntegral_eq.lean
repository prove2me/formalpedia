-- Prove2me | Theorems.Thm_PVM_represents_iff_unboundedIntegral_eq
-- name    : PVM.represents_iff_unboundedIntegral_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:11:37.482794+00:00
-- url     : https://prove2.me/theorems/5cfb2044-8f08-5061-acbd-3076164bb644
-- title:
--   PVM: represents iff unbounded Integral eq
-- statement:
--   For self-adjoint operators, the intrinsic and constructed spectral
--   integral formulations are logically equivalent.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Intrinsic.lean#L144-L150
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Intrinsic.lean#L144-L150

import Definitions.Def_Spectral_Spectral_Uniqueness
import Definitions.Def_Spectral_Spectral_Intrinsic
set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem PVM.represents_iff_unboundedIntegral_eq (E_pvm : PVM E)
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    E_pvm.Represents A ↔
      E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
        Complex.continuous_ofReal.measurable = A := by sorry
