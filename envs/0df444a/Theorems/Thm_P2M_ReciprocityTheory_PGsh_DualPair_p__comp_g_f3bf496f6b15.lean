-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair_p__comp_g_f3bf496f6b15
-- name    : P2M_ReciprocityTheory_PGsh_DualPair_p__comp_g_f3bf496f6b15
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:43:48.269344+00:00
-- url     : https://prove2.me/theorems/add59517-5f1b-56ca-a6b6-29b67d600c47
-- title:
--   P2 M Reciprocity Theory PGsh Dual Pair p  comp g f3bf496f6b15: P2 M Reciprocity Theory PGsh Dual Pair p  comp g f3bf496f6b15
-- statement:
--   The P2 M Reciprocity Theory PGsh Dual Pair p  comp g f3bf496f6b15 construction uses the P2 M Reciprocity Theory PGsh Dual Pair p  comp g f3bf496f6b15 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L170-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L170-L170

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

theorem P2M_ReciprocityTheory_PGsh_DualPair_p__comp_g_f3bf496f6b15 (c : (R : Type u)) : Dp.p₁L.comp (Dp.gL c) = Dp.μL c := by sorry

alias «ReciprocityTheory».«PGsh».«DualPair».«p₁_comp_g» := P2M_ReciprocityTheory_PGsh_DualPair_p__comp_g_f3bf496f6b15
