-- Prove2me | Theorems.Thm_UnipMove_GraphH_en_le_of_nsq
-- name    : UnipMove.GraphH.en_le_of_nsq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:11:43.549697+00:00
-- url     : https://prove2.me/theorems/d581c528-e587-445a-9347-70de12406e67
-- title:
--   Graph H: en le of nsq
-- statement:
--   The Graph H construction uses the en le of nsq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/BotMulVecExt.lean#L61-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/BotMulVecExt.lean#L61-L65

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove UnipMove.GraphH
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds NumberField Complex
open scoped ComplexConjugate Matrix
noncomputable section

theorem UnipMove.GraphH.en_le_of_nsq {m n : ℕ} (u : Fin m → ℂ) (v : Fin n → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (h : nsq u ≤ c ^ 2 * nsq v) : en u ≤ c * en v := by sorry
