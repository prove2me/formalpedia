-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair_mr____648a9fda1d75
-- name    : P2M_ReciprocityTheory_PGsh_DualPair_mr____648a9fda1d75
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:19:11.67841+00:00
-- url     : https://prove2.me/theorems/83da7a57-40aa-4e8e-8744-802d6bd07089
-- title:
--   P2 M Reciprocity Theory PGsh Dual Pair mr    648a9fda1d75: P2 M Reciprocity Theory PGsh Dual Pair mr    648a9fda1d75
-- statement:
--   The P2 M Reciprocity Theory PGsh Dual Pair mr    648a9fda1d75 construction uses the P2 M Reciprocity Theory PGsh Dual Pair mr    648a9fda1d75 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L161-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L161-L163

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

theorem P2M_ReciprocityTheory_PGsh_DualPair_mr____648a9fda1d75 (r t : (R : Type u)) :
    (Dp.mr r).1 (Dp.σ.1 t * Dp.η) = Dp.σ.1 r * (Dp.σ.1 t * Dp.η) := by sorry

alias «ReciprocityTheory».«PGsh».«DualPair».«mr_ση» := P2M_ReciprocityTheory_PGsh_DualPair_mr____648a9fda1d75
