-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair__L_zero_a2af1bc81e59
-- name    : P2M_ReciprocityTheory_PGsh_DualPair__L_zero_a2af1bc81e59
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:43:58.679706+00:00
-- url     : https://prove2.me/theorems/d95bb410-9386-4416-8c4d-b599b33b6d11
-- title:
--   P2 M Reciprocity Theory PGsh Dual Pair  L zero a2af1bc81e59: P2 M Reciprocity Theory PGsh Dual Pair  L zero a2af1bc81e59
-- statement:
--   The P2 M Reciprocity Theory PGsh Dual Pair  L zero a2af1bc81e59 construction uses the P2 M Reciprocity Theory PGsh Dual Pair  L zero a2af1bc81e59 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L86-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L86-L87

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_IsFibreSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.DualPair
variable {R : LAlg R₀} (Dp : DualPair R)

theorem P2M_ReciprocityTheory_PGsh_DualPair__L_zero_a2af1bc81e59 : Dp.μL 0 = Dp.σ.comp Dp.π := by sorry

alias «ReciprocityTheory».«PGsh».«DualPair».«μL_zero» := P2M_ReciprocityTheory_PGsh_DualPair__L_zero_a2af1bc81e59
