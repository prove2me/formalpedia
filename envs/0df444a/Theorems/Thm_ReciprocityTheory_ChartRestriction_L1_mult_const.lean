-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_mult_const
-- name    : ReciprocityTheory.ChartRestriction.L1.mult_const
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:27:35.434594+00:00
-- url     : https://prove2.me/theorems/280cfcc4-99d0-4b80-b3c9-dcc4e0511832
-- title:
--   L1: mult const
-- statement:
--   The L1 construction uses the mult const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffOneSubstOfConstantCoeffEqZero.lean#L80-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffOneSubstOfConstantCoeffEqZero.lean#L80-L86

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
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
variable {K : Type} [Field K] (g2 g3 : K)

theorem ReciprocityTheory.ChartRestriction.L1.mult_const (b : K) : constantCoeff ((uSer g2 g3).subst (C b * lgS g2 g3)) = 0 := by sorry
