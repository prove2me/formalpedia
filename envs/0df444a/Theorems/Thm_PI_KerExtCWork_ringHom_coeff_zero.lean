-- Prove2me | Theorems.Thm_PI_KerExtCWork_ringHom_coeff_zero
-- name    : PI.KerExtCWork.ringHom_coeff_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:33:24.556878+00:00
-- url     : https://prove2.me/theorems/c2c2614f-0327-5279-a0e2-6d0fd25bc027
-- title:
--   Ker Ext CWork: ring Hom coeff zero
-- statement:
--   The Ker Ext CWork construction uses the ring Hom coeff zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConstantCoefficientKernel/RingHomCoeffZero.lean#L9-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConstantCoefficientKernel/RingHomCoeffZero.lean#L9-L22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConstantCoefficientKernel_RingHomCoeffZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open PI PI.KerExtCWork

theorem PI.KerExtCWork.ringHom_coeff_zero {E : Type} [Field E] {n : Type} [Fintype n]
    (τ : n → E →+* ℂ) (hτ : Function.Injective τ) (c : n → ℂ)
    (h : ∀ e : E, ∑ i, c i * τ i e = 0) : c = 0 := by sorry
