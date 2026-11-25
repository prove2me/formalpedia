-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_isHeight_unique
-- name    : ReciprocityTheory.PGsh.BX.isHeight_unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:09.343849+00:00
-- url     : https://prove2.me/theorems/1f5bec61-dfa7-413d-8bdb-e21e869ae4d1
-- title:
--   BX: is Height unique
-- statement:
--   The BX construction uses the is Height unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsHeightUnique.lean#L67-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsHeightUnique.lean#L67-L70

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

theorem ReciprocityTheory.PGsh.BX.isHeight_unique (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) (y : B.G R) (hy : N • y = 0) (h h' : B.gg →ₗ[R₀] (R : Type u))
    (H : B.IsHeight Dp N y h) (H' : B.IsHeight Dp N y h') : h = h' := by sorry
