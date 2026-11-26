-- Prove2me | Theorems.Thm_PVM_selfAdjoint_le_coordinate_unboundedIntegral_of_cayley
-- name    : PVM.selfAdjoint_le_coordinate_unboundedIntegral_of_cayley
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:01:25.008056+00:00
-- url     : https://prove2.me/theorems/8ca4a516-9f25-52fe-af2a-8b0fea01d794
-- title:
--   PVM: self Adjoint le coordinate unbounded Integral of cayley
-- statement:
--   If a PVM integrates a bounded Cayley phase to the Cayley transform of a self-adjoint
--   operator, then that operator is contained in the PVM's coordinate integral.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/CayleyCalculus.lean#L90-L258
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/CayleyCalculus.lean#L90-L258

import Definitions.Def_Spectral_Cayley_Basic
import Definitions.Def_Spectral_PVM_Unbounded
import Definitions.Def_Spectral_Spectral_CayleyCalculus
set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem PVM.selfAdjoint_le_coordinate_unboundedIntegral_of_cayley
    (E_pvm : PVM E) (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (phase : ℝ → ℂ) (hphaseMeas : Measurable phase)
    (hphaseBdd : ∃ C, ∀ r, ‖phase r‖ ≤ C)
    (hphaseRelation : ∀ r : ℝ,
      (r : ℂ) * (1 - phase r) = Complex.I * (1 + phase r))
    (hphaseIntegral : E_pvm.integral phase hphaseMeas hphaseBdd =
      cayleyTransform A hA) :
    A ≤ E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable := by sorry
