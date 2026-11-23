-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_split
-- name    : ReciprocityTheory.L2DbarEstimates.split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:33:11.63986+00:00
-- url     : https://prove2.me/theorems/1e156fed-e69d-4f46-898a-ad4547a2431f
-- title:
--   L2 Dbar Estimates: split
-- statement:
--   The L2 Dbar Estimates construction uses the split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/MinimalSolutions/HormanderLemma.lean#L40-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/MinimalSolutions/HormanderLemma.lean#L40-L53

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_MinimalSolution
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HormanderLemma
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

theorem ReciprocityTheory.L2DbarEstimates.split (E H₁ H₂ : Type*) [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] :
    SplitStatement E H₁ H₂ := by sorry
