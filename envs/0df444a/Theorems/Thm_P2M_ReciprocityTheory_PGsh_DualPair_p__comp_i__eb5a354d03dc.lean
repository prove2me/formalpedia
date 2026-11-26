-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair_p__comp_i__eb5a354d03dc
-- name    : P2M_ReciprocityTheory_PGsh_DualPair_p__comp_i__eb5a354d03dc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:44:00.331386+00:00
-- url     : https://prove2.me/theorems/a633d396-ba6d-465e-8b4c-58497bad7921
-- title:
--   P2 M Reciprocity Theory PGsh Dual Pair p  comp i  eb5a354d03dc: P2 M Reciprocity Theory PGsh Dual Pair p  comp i  eb5a354d03dc
-- statement:
--   The P2 M Reciprocity Theory PGsh Dual Pair p  comp i  eb5a354d03dc construction uses the P2 M Reciprocity Theory PGsh Dual Pair p  comp i  eb5a354d03dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L169-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L169-L169

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

theorem P2M_ReciprocityTheory_PGsh_DualPair_p__comp_i__eb5a354d03dc : Dp.p₂L.comp Dp.i₂L = LHom.id Dp.D := by sorry

alias «ReciprocityTheory».«PGsh».«DualPair».«p₂_comp_i₂» := P2M_ReciprocityTheory_PGsh_DualPair_p__comp_i__eb5a354d03dc
