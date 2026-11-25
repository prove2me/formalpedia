-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_unramifiedCokernelLength_of_monomialDeterminant_frobeniusBlock_lengthBound
-- name    : ReciprocityTheory.PGsh.Up.unramifiedCokernelLength_of_monomialDeterminant_frobeniusBlock_lengthBound
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T18:17:19.415411+00:00
-- url     : https://prove2.me/theorems/99e1303f-f298-45aa-a4c0-b459416e5243
-- title:
--   Up: unramified Cokernel Length of monomial Determinant frobenius Block length Bound
-- statement:
--   The Up construction uses the unramified Cokernel Length of monomial Determinant frobenius Block length Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/FrobeniusOfGroupDivisorsRank.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/FrobeniusOfGroupDivisorsRank.lean#L30-L32

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

theorem ReciprocityTheory.PGsh.Up.unramifiedCokernelLength_of_monomialDeterminant_frobeniusBlock_lengthBound (hG : EmbeddingSeparatingGroupStatement) (hF1 : LiftMonomialDeterminantStatement) (hF2 : FrobeniusBlockStatement)
    (hF3 : FrobeniusLengthBoundStatement) : UnramifiedCokernelLengthStatement := by sorry
