-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair_fr___2154160be0da
-- name    : P2M_ReciprocityTheory_PGsh_DualPair_fr___2154160be0da
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:18:41.615972+00:00
-- url     : https://prove2.me/theorems/3b407b6d-641f-489d-a0af-74f2300b7391
-- title:
--   P2 M Reciprocity Theory PGsh Dual Pair fr   2154160be0da: P2 M Reciprocity Theory PGsh Dual Pair fr   2154160be0da
-- statement:
--   The P2 M Reciprocity Theory PGsh Dual Pair fr   2154160be0da construction uses the P2 M Reciprocity Theory PGsh Dual Pair fr   2154160be0da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean#L245-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean#L245-L250

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

theorem P2M_ReciprocityTheory_PGsh_DualPair_fr___2154160be0da (r : (R : Type u)) : (Dp.fr r).1 Dp.η = Dp.σ.1 r * Dp.η := by sorry

alias «ReciprocityTheory».«PGsh».«DualPair».«fr_η» := P2M_ReciprocityTheory_PGsh_DualPair_fr___2154160be0da
