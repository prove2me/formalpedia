-- Prove2me | Theorems.Thm_PI_CompDegEF_norm_natCast_pos
-- name    : PI.CompDegEF.norm_natCast_pos
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:32:05.870828+00:00
-- url     : https://prove2.me/theorems/88888fec-2513-4ab3-a0af-111a32f2c0dd
-- title:
--   Comp Deg EF: norm nat Cast pos
-- statement:
--   The Comp Deg EF construction uses the norm nat Cast pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionDegrees/NormLeOneOfInteger.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionDegrees/NormLeOneOfInteger.lean#L11-L13

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_DenseSurj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_NormLeOneOfInteger
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.CompDegEF
open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem PI.CompDegEF.norm_natCast_pos (l : ℕ) [hl : Fact l.Prime] : 0 < ‖((l : ℕ) : Om l)‖ := by sorry
