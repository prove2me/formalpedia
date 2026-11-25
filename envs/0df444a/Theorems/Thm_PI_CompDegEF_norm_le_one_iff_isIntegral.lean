-- Prove2me | Theorems.Thm_PI_CompDegEF_norm_le_one_iff_isIntegral
-- name    : PI.CompDegEF.norm_le_one_iff_isIntegral
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:26:26.228239+00:00
-- url     : https://prove2.me/theorems/b4e85de4-693d-52bc-bcf2-e77d42d9e1be
-- title:
--   Comp Deg EF: norm le one iff is Integral
-- statement:
--   The Comp Deg EF construction uses the norm le one iff is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionDegrees/MemIntegralClosureIffMemBall.lean#L50-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionDegrees/MemIntegralClosureIffMemBall.lean#L50-L69

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_DenseSurj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_MemIntegralClosureIffMemBall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.CompDegEF
open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
variable {l : ℕ} [hl : Fact l.Prime]

theorem PI.CompDegEF.norm_le_one_iff_isIntegral (z : Om l) : ‖z‖ ≤ 1 ↔ IsIntegral ℤ_[l] z := by sorry
