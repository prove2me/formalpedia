-- Prove2me | Theorems.Thm_PositivityTheory_CW_MaximumPrincipleOneFunction_hilbert_schmidt_nonneg_alt
-- name    : PositivityTheory.CW.MaximumPrincipleOneFunction.hilbert_schmidt_nonneg_alt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:51:37.091831+00:00
-- url     : https://prove2.me/theorems/55d525bf-1c12-4675-bffc-34cab6368531
-- title:
--   Maximum Principle One Function: hilbert schmidt nonneg alt
-- statement:
--   The Maximum Principle One Function construction uses the hilbert schmidt nonneg alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/MaximumPrincipleOfFacts.lean#L45-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/MaximumPrincipleOfFacts.lean#L45-L46

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_MaximumPrincipleOfFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.MaximumPrincipleOneFunction
variable {n : ℕ}

theorem PositivityTheory.CW.MaximumPrincipleOneFunction.hilbert_schmidt_nonneg_alt (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs2 g := by sorry
