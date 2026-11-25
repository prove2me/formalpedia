-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_PolynomialDegreeClosure_pd_prod
-- name    : PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure.pd_prod
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:31:00.265847+00:00
-- url     : https://prove2.me/theorems/20a0631b-ddf6-5450-8925-d1074adc7066
-- title:
--   Polynomial Degree Closure: pd prod
-- statement:
--   The Polynomial Degree Closure construction uses the pd prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/GfPolyA.lean#L61-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/GfPolyA.lean#L61-L70

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_GfPolyA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
variable {N : ℕ}

theorem PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure.pd_prod {ι : Type*} (s : Finset ι) (d : ι → ℕ) (P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ)
    (h : ∀ i ∈ s, IsPolyDeg (d i) (P i)) : IsPolyDeg (∑ i ∈ s, d i) (fun g => ∏ i ∈ s, P i g) := by sorry
