-- Prove2me | Theorems.Thm_PVM_phaseUnitaryGroup_generator
-- name    : PVM.phaseUnitaryGroup_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:10:34.521668+00:00
-- url     : https://prove2.me/theorems/8a3395e9-6db0-437a-abdd-532a7cc3f390
-- title:
--   PVM: phase Unitary Group generator
-- statement:
--   The generator of the phase unitary group is integration against the real coordinate.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Stone/Theorem.lean#L643-L647
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Stone/Theorem.lean#L643-L647

import Definitions.Def_Spectral_Stone_SelfAdjoint
import Definitions.Def_Spectral_Spectral_Existence
import Definitions.Def_Spectral_Stone_Theorem
set_option autoImplicit false
open MeasureTheory Filter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem PVM.phaseUnitaryGroup_generator (E_pvm : PVM E) :
    E_pvm.phaseUnitaryGroup.generator =
      E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
        Complex.continuous_ofReal.measurable := by sorry
