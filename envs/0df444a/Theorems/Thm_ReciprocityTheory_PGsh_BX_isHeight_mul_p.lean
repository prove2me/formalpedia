-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_isHeight_mul_p
-- name    : ReciprocityTheory.PGsh.BX.isHeight_mul_p
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:07:03.338941+00:00
-- url     : https://prove2.me/theorems/92be447f-e47b-40be-9970-9c8eb3bbd001
-- title:
--   BX: is Height mul p
-- statement:
--   The BX construction uses the is Height mul p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsHeightUnique.lean#L57-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsHeightUnique.lean#L57-L65

import Definitions.Def_ReciprocityTheory_DualLattices_HtLinStatement
import Definitions.Def_ReciprocityTheory_DualLattices_HeightFunctionalStatementOfPairingProperties
import Definitions.Def_ReciprocityTheory_DualLattices_IsHeightUnique
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
variable (B : BX R₀)

theorem ReciprocityTheory.PGsh.BX.isHeight_mul_p (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N p : ℕ)
    (hN : (N : (R : Type u)) = 0) (y : B.G R) (hy : (N * p) • y = 0) (h : B.gg →ₗ[R₀] (R : Type u))
    (H : B.IsHeight Dp (N * p) y h) : B.IsHeight Dp N (p • y) h := by sorry
