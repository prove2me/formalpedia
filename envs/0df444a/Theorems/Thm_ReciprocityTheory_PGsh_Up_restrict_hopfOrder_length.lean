-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_restrict_hopfOrder_length
-- name    : ReciprocityTheory.PGsh.Up.restrict_hopfOrder_length
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:10:06.412561+00:00
-- url     : https://prove2.me/theorems/869d489a-8706-49ea-840d-d4725de7d672
-- title:
--   Up: restrict hopf Order length
-- statement:
--   The Up construction uses the restrict hopf Order length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RestrictHopfOrderLength.lean#L22-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RestrictHopfOrderLength.lean#L22-L102

import Definitions.Def_ReciprocityTheory_DualLattices_RestrictedHopfOrderApproximationStatement
import Definitions.Def_ReciprocityTheory_DualLattices_MemAugIdeal
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsMatOfEquiv
import Definitions.Def_ReciprocityTheory_DualLattices_RestrictHopfOrderLength
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
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up.PullbackHopfOrder

theorem ReciprocityTheory.PGsh.Up.restrict_hopfOrder_length : RestrictedHopfOrderStatement := by sorry
