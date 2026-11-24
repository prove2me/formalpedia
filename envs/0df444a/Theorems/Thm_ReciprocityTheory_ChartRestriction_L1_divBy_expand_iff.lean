-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divBy_expand_iff
-- name    : ReciprocityTheory.ChartRestriction.L1.divBy_expand_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:43:25.762217+00:00
-- url     : https://prove2.me/theorems/f1509cfd-4368-44c3-b509-6f310ca3fb38
-- title:
--   L1: div By expand iff
-- statement:
--   The L1 construction uses the div By expand iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L221-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L221-L234

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem ReciprocityTheory.ChartRestriction.L1.divBy_expand_iff (x : K) (n : ℕ) (hn : n ≠ 0) (f : PowerSeries K) :
    DivBy x (f.subst ((X : PowerSeries K) ^ n)) ↔ DivBy x f := by sorry
