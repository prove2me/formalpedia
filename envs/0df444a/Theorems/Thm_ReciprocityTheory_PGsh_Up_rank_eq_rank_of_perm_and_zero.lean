-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_rank_eq_rank_of_perm_and_zero
-- name    : ReciprocityTheory.PGsh.Up.rank_eq_rank_of_perm_and_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:09:06.162252+00:00
-- url     : https://prove2.me/theorems/e476fbf4-a007-529b-b75f-57d655ddcfb8
-- title:
--   Up: rank eq rank of perm and zero
-- statement:
--   The Up construction uses the rank eq rank of perm and zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RankEqRankOfPermAndZero.lean#L222-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RankEqRankOfPermAndZero.lean#L222-L266

import Definitions.Def_ReciprocityTheory_DualLattices_EmbeddingSeparatingGroupStatement
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLengthOfLengthEigenLengthProduct
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
import Definitions.Def_ReciprocityTheory_DualLattices_RankMapLeRank
import Definitions.Def_ReciprocityTheory_DualLattices_RankEqRankOfPermAndZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2

theorem ReciprocityTheory.PGsh.Up.rank_eq_rank_of_perm_and_zero : EigenRankStatement := by sorry
