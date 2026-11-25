-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair_p__comp_g_24d4394e1bdb
-- name    : P2M_ReciprocityTheory_PGsh_DualPair_p__comp_g_24d4394e1bdb
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:44:04.55055+00:00
-- url     : https://prove2.me/theorems/cec047a2-bd82-4975-9bee-8ba73c274381
-- title:
--   P2 M Reciprocity Theory PGsh Dual Pair p  comp g 24d4394e1bdb: P2 M Reciprocity Theory PGsh Dual Pair p  comp g 24d4394e1bdb
-- statement:
--   The P2 M Reciprocity Theory PGsh Dual Pair p  comp g 24d4394e1bdb construction uses the P2 M Reciprocity Theory PGsh Dual Pair p  comp g 24d4394e1bdb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L171-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L171-L172

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

theorem P2M_ReciprocityTheory_PGsh_DualPair_p__comp_g_24d4394e1bdb (c : (R : Type u)) : Dp.p₂L.comp (Dp.gL c) = LHom.id Dp.D := by sorry

alias «ReciprocityTheory».«PGsh».«DualPair».«p₂_comp_g» := P2M_ReciprocityTheory_PGsh_DualPair_p__comp_g_24d4394e1bdb
