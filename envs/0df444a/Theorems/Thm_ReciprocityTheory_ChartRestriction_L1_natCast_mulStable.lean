-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_natCast_mulStable
-- name    : ReciprocityTheory.ChartRestriction.L1.natCast_mulStable
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:49:03.307959+00:00
-- url     : https://prove2.me/theorems/a8e441ca-e70f-57ab-bf26-ff4e8de6c9f4
-- title:
--   L1: nat Cast mul Stable
-- statement:
--   The L1 construction uses the nat Cast mul Stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedKerIdeal.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedKerIdeal.lean#L28-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKerPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedCardG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedGcd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKerIdeal
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

theorem ReciprocityTheory.ChartRestriction.L1.natCast_mulStable (L : PeriodPair) (n : ℕ) : MulStable L (n : ℂ) := by sorry
