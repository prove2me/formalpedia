-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair_mr___4f4cf4efc828
-- name    : P2M_ReciprocityTheory_PGsh_DualPair_mr___4f4cf4efc828
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:19:23.65625+00:00
-- url     : https://prove2.me/theorems/92261040-0615-4dd2-9029-621f83420a8f
-- title:
--   P2 M Reciprocity Theory PGsh Dual Pair mr   4f4cf4efc828: P2 M Reciprocity Theory PGsh Dual Pair mr   4f4cf4efc828
-- statement:
--   The P2 M Reciprocity Theory PGsh Dual Pair mr   4f4cf4efc828 construction uses the P2 M Reciprocity Theory PGsh Dual Pair mr   4f4cf4efc828 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L153-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L153-L154

import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.DualPair
variable {R : LAlg R₀} (Dp : DualPair R)

theorem P2M_ReciprocityTheory_PGsh_DualPair_mr___4f4cf4efc828 (r : (R : Type u)) (d : (Dp.D : Type u)) : Dp.π.1 ((Dp.mr r).1 d) = Dp.π.1 d := by sorry

alias «ReciprocityTheory».«PGsh».«DualPair».«mr_π» := P2M_ReciprocityTheory_PGsh_DualPair_mr___4f4cf4efc828
