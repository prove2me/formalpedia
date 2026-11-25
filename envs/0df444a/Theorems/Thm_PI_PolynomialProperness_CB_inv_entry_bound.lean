-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CB_inv_entry_bound
-- name    : PI.PolynomialProperness.CB.inv_entry_bound
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:02:58.862797+00:00
-- url     : https://prove2.me/theorems/75e09086-57f0-53f8-b21b-891e85e8de72
-- title:
--   CB: inv entry bound
-- statement:
--   The CB construction uses the inv entry bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/SecondOrderNormBound.lean#L111-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/SecondOrderNormBound.lean#L111-L116

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

theorem PI.PolynomialProperness.CB.inv_entry_bound {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hM : M.det = 1) {c : ℝ}
    (hc : ∀ i j, ‖M i j‖ ≤ c) (i j : Fin (n + 1)) : ‖M⁻¹ i j‖ ≤ n.factorial * c ^ n := by sorry
