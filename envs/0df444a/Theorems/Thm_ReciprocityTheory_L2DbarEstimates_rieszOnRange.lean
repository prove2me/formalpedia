-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_rieszOnRange
-- name    : ReciprocityTheory.L2DbarEstimates.rieszOnRange
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:03.697629+00:00
-- url     : https://prove2.me/theorems/ea65ba02-9864-4543-8ccd-cf75215daab2
-- title:
--   L2 Dbar Estimates: riesz On Range
-- statement:
--   The L2 Dbar Estimates construction uses the riesz On Range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/MinimalSolutions/MinimalSolution.lean#L7-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/MinimalSolutions/MinimalSolution.lean#L7-L56

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_MinimalSolutionStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_MinimalSolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open scoped InnerProductSpace

theorem ReciprocityTheory.L2DbarEstimates.rieszOnRange (E H : Type*) [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    RieszOnRangeStatement E H := by sorry
