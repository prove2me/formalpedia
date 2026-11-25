-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair_p__comp_i__b777ccf2ab69
-- name    : P2M_ReciprocityTheory_PGsh_DualPair_p__comp_i__b777ccf2ab69
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:43:54.675543+00:00
-- url     : https://prove2.me/theorems/194d2774-25d2-53bb-84b3-44827e6aea46
-- title:
--   P2 M Reciprocity Theory PGsh Dual Pair p  comp i  b777ccf2ab69: P2 M Reciprocity Theory PGsh Dual Pair p  comp i  b777ccf2ab69
-- statement:
--   The P2 M Reciprocity Theory PGsh Dual Pair p  comp i  b777ccf2ab69 construction uses the P2 M Reciprocity Theory PGsh Dual Pair p  comp i  b777ccf2ab69 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L168-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L168-L168

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

theorem P2M_ReciprocityTheory_PGsh_DualPair_p__comp_i__b777ccf2ab69 : Dp.p₁L.comp Dp.i₂L = Dp.σ.comp Dp.π := by sorry

alias «ReciprocityTheory».«PGsh».«DualPair».«p₁_comp_i₂» := P2M_ReciprocityTheory_PGsh_DualPair_p__comp_i__b777ccf2ab69
