-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_frobenius_of_length_lifts
-- name    : ReciprocityTheory.PGsh.Up.frobenius_of_length_lifts
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T18:12:12.188686+00:00
-- url     : https://prove2.me/theorems/5a344aa4-9bf6-5495-ac90-f9b9f39cbca7
-- title:
--   Up: frobenius of length lifts
-- statement:
--   The Up construction uses the frobenius of length lifts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/FrobeniusOfGroupDivisorsRank.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/FrobeniusOfGroupDivisorsRank.lean#L17-L20

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

theorem ReciprocityTheory.PGsh.Up.frobenius_of_length_lifts (hLen : LenIdStatement) (hEx : LenExStatement) (hTot : EigenLengthProductStatement)
    (hG : EmbeddingSeparatingGroupStatement) (hE : EigenElementaryDivisorStatement) (hR : EigenRankStatement)
    (hB : EigenLiftsBasisStatement) (hF : EigenLiftsFrobeniusStatement) : UnramifiedCokernelLengthStatement := by sorry
