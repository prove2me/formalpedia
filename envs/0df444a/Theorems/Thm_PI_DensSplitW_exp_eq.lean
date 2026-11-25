-- Prove2me | Theorems.Thm_PI_DensSplitW_exp_eq
-- name    : PI.DensSplitW.exp_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:26:24.342598+00:00
-- url     : https://prove2.me/theorems/b6ad19d3-fa33-5f1b-9096-66c0092a11f4
-- title:
--   Dens Split W: exp eq
-- statement:
--   The Dens Split W construction uses the exp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitDensity/PhiXFinrankRange.lean#L113-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitDensity/PhiXFinrankRange.lean#L113-L119

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

theorem PI.DensSplitW.exp_eq (n m r : ℕ) (hmn : m ≤ n) (hrm : r ≤ m) :
    n * m + r * (n - m) + (n - m) * (m - r) = 2 * n * m - m ^ 2 := by sorry
