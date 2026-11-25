-- Prove2me | Theorems.Thm_PI_GGRatio_pow_gauss_eq_prod
-- name    : PI.GGRatio.pow_gauss_eq_prod
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:31:09.472804+00:00
-- url     : https://prove2.me/theorems/6bd8496c-b80e-4670-b943-01e2f0f39ddb
-- title:
--   GGRatio: pow gauss eq prod
-- statement:
--   The GGRatio construction uses the pow gauss eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GenericRatioBound/GenericRatioOfBound.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GenericRatioBound/GenericRatioOfBound.lean#L14-L15

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GenericRatioBound_GenericRatioOfBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.GGRatio
open Finset

theorem PI.GGRatio.pow_gauss_eq_prod (q : ℝ) (k : ℕ) : q ^ (k * (k - 1) / 2) = ∏ i ∈ Ico 1 k, q ^ i := by sorry
