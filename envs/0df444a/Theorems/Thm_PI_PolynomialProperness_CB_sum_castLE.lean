-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CB_sum_castLE
-- name    : PI.PolynomialProperness.CB.sum_castLE
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:38:11.899875+00:00
-- url     : https://prove2.me/theorems/8796f867-9a1f-4f14-a8d2-0902b9ab61d9
-- title:
--   CB: sum cast LE
-- statement:
--   The CB construction uses the sum cast LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/SecondOrderNormBound.lean#L9-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/SecondOrderNormBound.lean#L9-L17

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

theorem PI.PolynomialProperness.CB.sum_castLE {m n : ℕ} (h : n ≤ m) (f : Fin m → ℂ) (hf : ∀ l : Fin m, n ≤ l.val → f l = 0) :
    ∑ l, f l = ∑ t : Fin n, f (Fin.castLE h t) := by sorry
