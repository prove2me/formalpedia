-- Prove2me | Theorems.Thm_PI_DensSplitW_sub_factor
-- name    : PI.DensSplitW.sub_factor
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:26:41.899932+00:00
-- url     : https://prove2.me/theorems/ea2365f9-bb8a-4af4-a918-174cba8e3137
-- title:
--   Dens Split W: sub factor
-- statement:
--   The Dens Split W construction uses the sub factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitDensity/PhiXFinrankRange.lean#L95-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitDensity/PhiXFinrankRange.lean#L95-L103

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_FiberCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_PhiXFinrankRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.L2.SG.DensExact
open PI PI.DensSplitW

theorem PI.DensSplitW.sub_factor (q N i : ℕ) (hq : 0 < q) (hi : i ≤ N) :
    ((q ^ N - q ^ i : ℕ) : ℝ) = (q : ℝ) ^ N * (1 - ((q : ℝ) ^ (N - i))⁻¹) := by sorry
