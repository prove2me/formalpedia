-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair_p__comp_i__dfbf9aefdac4
-- name    : P2M_ReciprocityTheory_PGsh_DualPair_p__comp_i__dfbf9aefdac4
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:44:01.542792+00:00
-- url     : https://prove2.me/theorems/36e99118-61a8-5570-aaaf-ec0308ba95d2
-- title:
--   P2 M Reciprocity Theory PGsh Dual Pair p  comp i  dfbf9aefdac4: P2 M Reciprocity Theory PGsh Dual Pair p  comp i  dfbf9aefdac4
-- statement:
--   The P2 M Reciprocity Theory PGsh Dual Pair p  comp i  dfbf9aefdac4 construction uses the P2 M Reciprocity Theory PGsh Dual Pair p  comp i  dfbf9aefdac4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L167-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L167-L167

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

theorem P2M_ReciprocityTheory_PGsh_DualPair_p__comp_i__dfbf9aefdac4 : Dp.p₂L.comp Dp.i₁L = Dp.σ.comp Dp.π := by sorry

alias «ReciprocityTheory».«PGsh».«DualPair».«p₂_comp_i₁» := P2M_ReciprocityTheory_PGsh_DualPair_p__comp_i__dfbf9aefdac4
