-- Prove2me | Theorems.Thm_PI_EF_localLemma_of_helpers
-- name    : PI.EF.localLemma_of_helpers
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:44.000254+00:00
-- url     : https://prove2.me/theorems/dc332434-6900-578f-bcff-a0642319e9f4
-- title:
--   EF: local Lemma of helpers
-- statement:
--   The EF construction uses the local Lemma of helpers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LocalLemmaOfHelpers.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LocalLemmaOfHelpers.lean#L14-L19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DiscIn
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindowIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_Assemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronGlue
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LocalProofs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LogWindowLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthFinal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LocalLemmaOfHelpers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF

theorem PI.EF.localLemma_of_helpers (hZW : PI.ZerosWindow) (hDF : PI.DiscFactor) (hDL : PI.DiscLog)
    (hLB : PI.LBoundRight) (hZB : PI.ZetaBoundRight) (hLI : PI.LInvRight) :
    ∃ C, 0 < C ∧ LocalLemma C := by sorry
