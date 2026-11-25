-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integralClosureRank_and_residueTrdegLe
-- name    : ReciprocityTheory.MultiplicativeHeights.integralClosureRank_and_residueTrdegLe
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:09.785652+00:00
-- url     : https://prove2.me/theorems/17e37bb7-45f1-448b-a945-f877692949ca
-- title:
--   Multiplicative Heights: integral Closure Rank and residue Trdeg Le
-- statement:
--   The Multiplicative Heights construction uses the integral Closure Rank and residue Trdeg Le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/IntegralClosureRankAndResidueTrdegLe.lean#L143-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/IntegralClosureRankAndResidueTrdegLe.lean#L143-L144

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntegralClosureRankAndResidueTrdegLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial

theorem ReciprocityTheory.MultiplicativeHeights.integralClosureRank_and_residueTrdegLe : DedekindRankStatement ∧ TRStatement := by sorry
