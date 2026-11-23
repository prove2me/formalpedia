-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_DualPair_mr_apply
-- name    : ReciprocityTheory.PGsh.DualPair.mr_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:32:59.512163+00:00
-- url     : https://prove2.me/theorems/622f41bb-e07f-4511-8865-25993ca248f6
-- title:
--   Dual Pair: mr apply
-- statement:
--   The Dual Pair construction uses the mr apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L150-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L150-L151

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

theorem ReciprocityTheory.PGsh.DualPair.mr_apply (r : (R : Type u)) (d : (Dp.D : Type u)) :
    (Dp.mr r).1 d = Dp.σ.1 (Dp.π.1 d) + Dp.σ.1 r * (d - Dp.σ.1 (Dp.π.1 d)) := by sorry
