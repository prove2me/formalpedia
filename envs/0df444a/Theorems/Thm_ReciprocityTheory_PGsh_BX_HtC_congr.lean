-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_HtC_congr
-- name    : ReciprocityTheory.PGsh.BX.HtC_congr
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:05:06.977123+00:00
-- url     : https://prove2.me/theorems/f34dfe8f-2ea0-58d9-83e8-393e99649c92
-- title:
--   BX: Ht C congr
-- statement:
--   The BX construction uses the Ht C congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NsmulTensorEqZero.lean#L95-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NsmulTensorEqZero.lean#L95-L98

import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulTensorEqZero
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
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀) {R : LAlg R₀} (Dp : DualPair R)

theorem ReciprocityTheory.PGsh.BX.HtC_congr {N : ℕ} {y : B.G R} {x x' : B.G Dp.D} {E E' : (Dp.D : Type u)} (hx : x = x')
    (hE : E = E') : B.HtC Dp N y x E → B.HtC Dp N y x' E' := by sorry
