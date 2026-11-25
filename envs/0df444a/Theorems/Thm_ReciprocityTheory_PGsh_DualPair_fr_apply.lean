-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_DualPair_fr_apply
-- name    : ReciprocityTheory.PGsh.DualPair.fr_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:06:11.987856+00:00
-- url     : https://prove2.me/theorems/94518b57-10b5-4ece-8da9-bfacc037c4bf
-- title:
--   Dual Pair: fr apply
-- statement:
--   The Dual Pair construction uses the fr apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean#L234-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean#L234-L235

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

theorem ReciprocityTheory.PGsh.DualPair.fr_apply (r : (R : Type u)) (b : (Dp.D : Type u)) :
    (Dp.fr r).1 b = Dp.σ.1 (Dp.π.1 b) + Dp.σ.1 (Dp.κ b * r) * Dp.η := by sorry
