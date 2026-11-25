-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CB_mx_transpose
-- name    : PI.PolynomialProperness.CB.mx_transpose
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:37:56.081866+00:00
-- url     : https://prove2.me/theorems/f81cc91c-9da3-5d74-a0b1-a09a7133a456
-- title:
--   CB: mx transpose
-- statement:
--   The CB construction uses the mx transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/SecondOrderNormBound.lean#L71-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/SecondOrderNormBound.lean#L71-L77

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_SecondOrderNormBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.CB

theorem PI.PolynomialProperness.CB.mx_transpose {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : mx Mᵀ = mx M := by sorry
