-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_isHeight_map
-- name    : ReciprocityTheory.PGsh.BX.isHeight_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:51.789471+00:00
-- url     : https://prove2.me/theorems/7c45be33-9d0d-437b-a54d-84ce2faca53d
-- title:
--   BX: is Height map
-- statement:
--   The BX construction uses the is Height map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsHeightUnique.lean#L21-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsHeightUnique.lean#L21-L46

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

theorem ReciprocityTheory.PGsh.BX.isHeight_map (hB1 : PairingPropertiesStatement B) {R S : LAlg R₀} (Dp : DualPair R) (Dq : DualPair S)
    (g : LHom R S) (f : LHom Dp.D Dq.D) (hfπ : ∀ x, Dq.π.1 (f.1 x) = g.1 (Dp.π.1 x))
    (hfσ : ∀ x, f.1 (Dp.σ.1 x) = Dq.σ.1 (g.1 x)) (hfη : f.1 Dp.η = Dq.η) (N : ℕ) (y : B.G R)
    (h : B.gg →ₗ[R₀] (R : Type u)) (H : B.IsHeight Dp N y h) :
    B.IsHeight Dq N (B.map g y) (g.1.toLinearMap ∘ₗ h) := by sorry
