-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair___comp_fr_8c3b9426a108
-- name    : P2M_ReciprocityTheory_PGsh_DualPair___comp_fr_8c3b9426a108
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:18:33.756399+00:00
-- url     : https://prove2.me/theorems/5d046133-7c30-5f97-8e75-a3ba50a48be7
-- title:
--   P2 M Reciprocity Theory PGsh Dual Pair   comp fr 8c3b9426a108: P2 M Reciprocity Theory PGsh Dual Pair   comp fr 8c3b9426a108
-- statement:
--   The P2 M Reciprocity Theory PGsh Dual Pair   comp fr 8c3b9426a108 construction uses the P2 M Reciprocity Theory PGsh Dual Pair   comp fr 8c3b9426a108 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean#L237-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean#L237-L239

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
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

theorem P2M_ReciprocityTheory_PGsh_DualPair___comp_fr_8c3b9426a108 (r : (R : Type u)) : Dp.π.comp (Dp.fr r) = Dp.π := by sorry

alias «ReciprocityTheory».«PGsh».«DualPair».«π_comp_fr» := P2M_ReciprocityTheory_PGsh_DualPair___comp_fr_8c3b9426a108
