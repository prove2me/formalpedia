-- Prove2me | Theorems.Thm_PI_GGRatio_ratio_le
-- name    : PI.GGRatio.ratio_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:57:46.727884+00:00
-- url     : https://prove2.me/theorems/2e4d96a3-b000-5548-b898-ede31d952620
-- title:
--   GGRatio: ratio le
-- statement:
--   The GGRatio construction uses the ratio le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GenericRatioBound/GenericRatioOfBound.lean#L22-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GenericRatioBound/GenericRatioOfBound.lean#L22-L46

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

theorem PI.GGRatio.ratio_le (q k d : ℕ) (hq : 2 ≤ q) (hd : ∏ i ∈ Ico 1 k, (q ^ i - 1) ≤ d) :
    ((q ^ (k * (k - 1) / 2) : ℕ) : ℝ) / (d : ℝ) ≤ ∏ i ∈ Ico 1 k, (1 - ((q : ℝ) ^ i)⁻¹)⁻¹ := by sorry
