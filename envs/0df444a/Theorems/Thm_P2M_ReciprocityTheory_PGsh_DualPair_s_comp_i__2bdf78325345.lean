-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair_s_comp_i__2bdf78325345
-- name    : P2M_ReciprocityTheory_PGsh_DualPair_s_comp_i__2bdf78325345
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:44:07.089018+00:00
-- url     : https://prove2.me/theorems/e75cf22a-11c8-5192-bdca-21f89a45dd05
-- title:
--   P2 M Reciprocity Theory PGsh Dual Pair s comp i  2bdf78325345: P2 M Reciprocity Theory PGsh Dual Pair s comp i  2bdf78325345
-- statement:
--   The P2 M Reciprocity Theory PGsh Dual Pair s comp i  2bdf78325345 construction uses the P2 M Reciprocity Theory PGsh Dual Pair s comp i  2bdf78325345 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L174-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L174-L176

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

theorem P2M_ReciprocityTheory_PGsh_DualPair_s_comp_i__2bdf78325345 : Dp.sL.comp Dp.i₁L = LHom.id Dp.D := by sorry

alias «ReciprocityTheory».«PGsh».«DualPair».«s_comp_i₁» := P2M_ReciprocityTheory_PGsh_DualPair_s_comp_i__2bdf78325345
