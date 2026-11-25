-- Prove2me | Theorems.Thm_PI_DensSplitW_prod_factor
-- name    : PI.DensSplitW.prod_factor
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:26:30.957162+00:00
-- url     : https://prove2.me/theorems/db44c760-41c5-5727-8f9e-35367764d352
-- title:
--   Dens Split W: prod factor
-- statement:
--   The Dens Split W construction uses the prod factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitDensity/PhiXFinrankRange.lean#L105-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitDensity/PhiXFinrankRange.lean#L105-L111

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

theorem PI.DensSplitW.prod_factor (q b c : ℕ) (hq : 0 < q) (hc : c ≤ b) :
    ((∏ i ∈ range c, (q ^ b - q ^ i) : ℕ) : ℝ) =
      (q : ℝ) ^ (b * c) * ∏ i ∈ range c, (1 - ((q : ℝ) ^ (b - i))⁻¹) := by sorry
