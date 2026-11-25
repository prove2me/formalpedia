-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul_tg_eta
-- name    : ReciprocityTheory.PGsh.BX.nsmul_tg_eta
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:06:00.851835+00:00
-- url     : https://prove2.me/theorems/6d724579-7e04-5b34-a2b9-b1e0ba2bdd4e
-- title:
--   BX: nsmul tg eta
-- statement:
--   The BX construction uses the nsmul tg eta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsHeightUnique.lean#L48-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsHeightUnique.lean#L48-L55

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

theorem ReciprocityTheory.PGsh.BX.nsmul_tg_eta {R : LAlg R₀} (Dp : DualPair R) (N : ℕ) (hN : (N : (R : Type u)) = 0) (v : B.gg) :
    N • B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk) = 0 := by sorry
