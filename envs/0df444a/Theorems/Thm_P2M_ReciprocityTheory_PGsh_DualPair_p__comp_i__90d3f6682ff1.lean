-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair_p__comp_i__90d3f6682ff1
-- name    : P2M_ReciprocityTheory_PGsh_DualPair_p__comp_i__90d3f6682ff1
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:43:47.274074+00:00
-- url     : https://prove2.me/theorems/d75e5c56-b342-543b-aa0a-0937dc04bb3f
-- title:
--   P2 M Reciprocity Theory PGsh Dual Pair p  comp i  90d3f6682ff1: P2 M Reciprocity Theory PGsh Dual Pair p  comp i  90d3f6682ff1
-- statement:
--   The P2 M Reciprocity Theory PGsh Dual Pair p  comp i  90d3f6682ff1 construction uses the P2 M Reciprocity Theory PGsh Dual Pair p  comp i  90d3f6682ff1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L166-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L166-L166

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

theorem P2M_ReciprocityTheory_PGsh_DualPair_p__comp_i__90d3f6682ff1 : Dp.p₁L.comp Dp.i₁L = LHom.id Dp.D := by sorry

alias «ReciprocityTheory».«PGsh».«DualPair».«p₁_comp_i₁» := P2M_ReciprocityTheory_PGsh_DualPair_p__comp_i__90d3f6682ff1
