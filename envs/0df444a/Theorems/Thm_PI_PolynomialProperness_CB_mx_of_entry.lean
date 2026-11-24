-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CB_mx_of_entry
-- name    : PI.PolynomialProperness.CB.mx_of_entry
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:56:40.408617+00:00
-- url     : https://prove2.me/theorems/b4727464-3d43-4a4a-b48a-5320f79b63cc
-- title:
--   CB: mx of entry
-- statement:
--   The CB construction uses the mx of entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/SecondOrderNormBound.lean#L118-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/SecondOrderNormBound.lean#L118-L119

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

theorem PI.PolynomialProperness.CB.mx_of_entry {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j, ‖M i j‖ ≤ c) : mx M ≤ c := by sorry
