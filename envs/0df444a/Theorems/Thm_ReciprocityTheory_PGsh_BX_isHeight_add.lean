-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_isHeight_add
-- name    : ReciprocityTheory.PGsh.BX.isHeight_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:29:25.220025+00:00
-- url     : https://prove2.me/theorems/e05af309-55bc-42ed-9aac-787a170ca73c
-- title:
--   BX: is Height add
-- statement:
--   The BX construction uses the is Height add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsHeightUnique.lean#L77-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsHeightUnique.lean#L77-L80

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

theorem ReciprocityTheory.PGsh.BX.isHeight_add (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) {y y' : B.G R} {h h' : B.gg →ₗ[R₀] (R : Type u)}
    (H : B.IsHeight Dp N y h) (H' : B.IsHeight Dp N y' h') : B.IsHeight Dp N (y + y') (h + h') := by sorry
