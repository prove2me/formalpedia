-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair___ker_0eced12ea04a
-- name    : P2M_ReciprocityTheory_PGsh_DualPair___ker_0eced12ea04a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:18:37.101716+00:00
-- url     : https://prove2.me/theorems/9d9b8034-4d7c-5e2c-8b53-1f99acc6ae3b
-- title:
--   P2 M Reciprocity Theory PGsh Dual Pair   ker 0eced12ea04a: P2 M Reciprocity Theory PGsh Dual Pair   ker 0eced12ea04a
-- statement:
--   The P2 M Reciprocity Theory PGsh Dual Pair   ker 0eced12ea04a construction uses the P2 M Reciprocity Theory PGsh Dual Pair   ker 0eced12ea04a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L36-L37

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

theorem P2M_ReciprocityTheory_PGsh_DualPair___ker_0eced12ea04a : Dp.η ∈ RingHom.ker Dp.π.1 := by sorry

alias «ReciprocityTheory».«PGsh».«DualPair».«η_ker» := P2M_ReciprocityTheory_PGsh_DualPair___ker_0eced12ea04a
