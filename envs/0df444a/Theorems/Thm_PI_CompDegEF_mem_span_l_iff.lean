-- Prove2me | Theorems.Thm_PI_CompDegEF_mem_span_l_iff
-- name    : PI.CompDegEF.mem_span_l_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:27:39.490794+00:00
-- url     : https://prove2.me/theorems/74c811f1-6902-408a-a9b2-98aa38701116
-- title:
--   Comp Deg EF: mem span l iff
-- statement:
--   The Comp Deg EF construction uses the mem span l iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionDegrees/MemSpanLIff.lean#L9-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionDegrees/MemSpanLIff.lean#L9-L38

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_DenseSurj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_MemSpanLIff
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

theorem PI.CompDegEF.mem_span_l_iff {l : ℕ} [hl : Fact l.Prime] (K : FinExt l) (y : ↥(ball K)) :
    y ∈ Ideal.span {((l : ℕ) : ↥(ball K))} ↔
      ‖((y : ↥K.1) : Om l)‖ ≤ ‖((l : ℕ) : Om l)‖ := by sorry
