-- Prove2me | Theorems.Thm_PI_Residue_tsum_pi_prod
-- name    : PI.Residue.tsum_pi_prod
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:20:03.357485+00:00
-- url     : https://prove2.me/theorems/0d68c34b-f847-4d1d-b719-53813adc4e13
-- title:
--   Residue: tsum pi prod
-- statement:
--   The Residue construction uses the tsum pi prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/FactorizationMultisetProd.lean#L89-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/FactorizationMultisetProd.lean#L89-L97

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_FactorizationMultisetProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Residue
open scoped ENNReal

theorem PI.Residue.tsum_pi_prod (w : ℕ → ℝ≥0∞) (m : ℕ) :
    ∑' v : Fin m → ℕ, ∏ i, w (v i) = (∑' n, w n) ^ m := by sorry
