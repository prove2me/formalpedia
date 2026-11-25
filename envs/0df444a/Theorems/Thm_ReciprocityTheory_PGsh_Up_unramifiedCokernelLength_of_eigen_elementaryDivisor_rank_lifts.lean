-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_unramifiedCokernelLength_of_eigen_elementaryDivisor_rank_lifts
-- name    : ReciprocityTheory.PGsh.Up.unramifiedCokernelLength_of_eigen_elementaryDivisor_rank_lifts
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T18:19:07.714337+00:00
-- url     : https://prove2.me/theorems/cb91976a-c821-57a1-abe7-f3b720d5c95d
-- title:
--   Up: unramified Cokernel Length of eigen elementary Divisor rank lifts
-- statement:
--   The Up construction uses the unramified Cokernel Length of eigen elementary Divisor rank lifts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/FrobeniusOfGroupDivisorsRank.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/FrobeniusOfGroupDivisorsRank.lean#L22-L24

import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLengthOfLengthEigenLengthProduct
import Definitions.Def_ReciprocityTheory_DualLattices_EqZeroOfIsoZero
import Definitions.Def_ReciprocityTheory_DualLattices_MatEquivApply
import Definitions.Def_ReciprocityTheory_DualLattices_EigenLengthProductStatementHolds
import Definitions.Def_ReciprocityTheory_DualLattices_LenEx
import Definitions.Def_ReciprocityTheory_DualLattices_MonomialsSpanOfProdEq
import Definitions.Def_ReciprocityTheory_DualLattices_EigenLiftsFrobenius
import Definitions.Def_ReciprocityTheory_DualLattices_ElementaryDivisorStatement
import Definitions.Def_ReciprocityTheory_DualLattices_RankEqRankOfPermAndZero
import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatementHolds
import Definitions.Def_ReciprocityTheory_DualLattices_FrobeniusBlock
import Definitions.Def_ReciprocityTheory_DualLattices_SumX
import Definitions.Def_ReciprocityTheory_DualLattices_EmbeddingSeparatingGroup
import Definitions.Def_ReciprocityTheory_DualLattices_FrobeniusOfGroupDivisorsRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up

theorem ReciprocityTheory.PGsh.Up.unramifiedCokernelLength_of_eigen_elementaryDivisor_rank_lifts (hG : EmbeddingSeparatingGroupStatement) (hE : EigenElementaryDivisorStatement)
    (hR : EigenRankStatement) (hB : EigenLiftsBasisStatement) (hF : EigenLiftsFrobeniusStatement) : UnramifiedCokernelLengthStatement := by sorry
