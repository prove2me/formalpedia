-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_permutedCokernelLowerBound_of
-- name    : ReciprocityTheory.PGsh.Up.permutedCokernelLowerBound_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:55.279376+00:00
-- url     : https://prove2.me/theorems/7525392c-9cf2-4498-8323-2b48d8ff82b2
-- title:
--   Up: permuted Cokernel Lower Bound of
-- statement:
--   The Up construction uses the permuted Cokernel Lower Bound of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UnramifiedCokernelLowerBoundOf.lean#L160-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UnramifiedCokernelLowerBoundOf.lean#L160-L175

import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundStatement
import Definitions.Def_ReciprocityTheory_DualLattices_MapSmulOneMulVec
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundOf
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

theorem ReciprocityTheory.PGsh.Up.permutedCokernelLowerBound_of (hU6 : CokernelLengthComparisonStatement) (hEx : LenExStatement) (hKG : KilledGenStatement)
    (hIG : IdemGenStatement) : PermutedCokernelLowerBoundStatement := by sorry
