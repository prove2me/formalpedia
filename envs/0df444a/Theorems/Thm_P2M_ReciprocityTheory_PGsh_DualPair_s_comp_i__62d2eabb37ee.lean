-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair_s_comp_i__62d2eabb37ee
-- name    : P2M_ReciprocityTheory_PGsh_DualPair_s_comp_i__62d2eabb37ee
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:43:33.094252+00:00
-- url     : https://prove2.me/theorems/64ae09d2-b847-5222-90c9-0a499ce3607b
-- title:
--   P2 M Reciprocity Theory PGsh Dual Pair s comp i  62d2eabb37ee: P2 M Reciprocity Theory PGsh Dual Pair s comp i  62d2eabb37ee
-- statement:
--   The P2 M Reciprocity Theory PGsh Dual Pair s comp i  62d2eabb37ee construction uses the P2 M Reciprocity Theory PGsh Dual Pair s comp i  62d2eabb37ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L178-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L178-L180

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

theorem P2M_ReciprocityTheory_PGsh_DualPair_s_comp_i__62d2eabb37ee : Dp.sL.comp Dp.i₂L = LHom.id Dp.D := by sorry

alias «ReciprocityTheory».«PGsh».«DualPair».«s_comp_i₂» := P2M_ReciprocityTheory_PGsh_DualPair_s_comp_i__62d2eabb37ee
