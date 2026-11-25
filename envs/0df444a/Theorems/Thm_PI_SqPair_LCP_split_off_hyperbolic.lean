-- Prove2me | Theorems.Thm_PI_SqPair_LCP_split_off_hyperbolic
-- name    : PI.SqPair.LCP.split_off_hyperbolic
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:31:28.33928+00:00
-- url     : https://prove2.me/theorems/b27a4c0c-5cce-48c3-b6b7-5cfc97883d5c
-- title:
--   LCP: split off hyperbolic
-- statement:
--   The LCP construction uses the split off hyperbolic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/SplOff.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/SplOff.lean#L8-L11

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_SplPlane
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_SplOff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SqPair PI.SqPair.LCP

theorem PI.SqPair.LCP.split_off_hyperbolic : SplitOff := by sorry
