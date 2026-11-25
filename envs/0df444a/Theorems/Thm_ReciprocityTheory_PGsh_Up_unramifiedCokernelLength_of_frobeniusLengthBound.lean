-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_unramifiedCokernelLength_of_frobeniusLengthBound
-- name    : ReciprocityTheory.PGsh.Up.unramifiedCokernelLength_of_frobeniusLengthBound
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T18:13:52.258019+00:00
-- url     : https://prove2.me/theorems/ec1f6dfd-0cb4-4290-ae0c-8b1bd965bb65
-- title:
--   Up: unramified Cokernel Length of frobenius Length Bound
-- statement:
--   The Up construction uses the unramified Cokernel Length of frobenius Length Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/FrobeniusOfGroupDivisorsRank.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/FrobeniusOfGroupDivisorsRank.lean#L34-L35

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

theorem ReciprocityTheory.PGsh.Up.unramifiedCokernelLength_of_frobeniusLengthBound (hG : EmbeddingSeparatingGroupStatement) (hF3 : FrobeniusLengthBoundStatement) : UnramifiedCokernelLengthStatement := by sorry
