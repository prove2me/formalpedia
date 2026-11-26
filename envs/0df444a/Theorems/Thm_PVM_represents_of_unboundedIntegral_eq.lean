-- Prove2me | Theorems.Thm_PVM_represents_of_unboundedIntegral_eq
-- name    : PVM.represents_of_unboundedIntegral_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:12:05.826361+00:00
-- url     : https://prove2.me/theorems/e972c6a6-1df3-4ba6-800c-6a30afd1f59d
-- title:
--   PVM: represents of unbounded Integral eq
-- statement:
--   Equality with the coordinate spectral integral supplies an intrinsic
--   representation.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Intrinsic.lean#L38-L51
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Intrinsic.lean#L38-L51

import Definitions.Def_Spectral_Spectral_Uniqueness
import Definitions.Def_Spectral_Spectral_Intrinsic
set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem PVM.represents_of_unboundedIntegral_eq (E_pvm : PVM E)
    (A : E →ₗ.[ℂ] E)
    (h : E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable = A) :
    E_pvm.Represents A := by sorry
