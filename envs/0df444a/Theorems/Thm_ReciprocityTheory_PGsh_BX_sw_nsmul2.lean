-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_sw_nsmul2
-- name    : ReciprocityTheory.PGsh.BX.sw_nsmul2
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:05:40.763544+00:00
-- url     : https://prove2.me/theorems/32ebd04e-f750-53cd-8873-bf34be10bea5
-- title:
--   BX: sw nsmul2
-- statement:
--   The BX construction uses the sw nsmul2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsPairingValueAddRight.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsPairingValueAddRight.lean#L62-L64

import Definitions.Def_ReciprocityTheory_DualLattices_SeriesState
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulFstAddSnd
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
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
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀) {R : LAlg R₀}

theorem ReciprocityTheory.PGsh.BX.sw_nsmul2 {x y : B.G R} (u : B.P R x y) (n : ℕ) :
    B.sw (B.nsmul2 u n) = B.nsmul1 (B.sw u) n := by sorry
