-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_g2_eq_zero_of_hasCMBy_three
-- name    : ReciprocityTheory.ChartRestriction.L1.g2_eq_zero_of_hasCMBy_three
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:51:49.344638+00:00
-- url     : https://prove2.me/theorems/9e60c805-f110-4af9-9b71-639d662f89c7
-- title:
--   L1: g2 eq zero of has CMBy three
-- statement:
--   The L1 construction uses the g2 eq zero of has CMBy three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/G2EqZeroOfHasCMByThree.lean#L29-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/G2EqZeroOfHasCMByThree.lean#L29-L57

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_G2EqZeroOfHasCMByThree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.g2_eq_zero_of_hasCMBy_three (L : PeriodPair) (hCM : HasCMBy 3 L) : L.g₂ = 0 := by sorry
