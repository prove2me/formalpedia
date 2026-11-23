-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_pairing_sw
-- name    : ReciprocityTheory.PGsh.BX.pairing_sw
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:12.615598+00:00
-- url     : https://prove2.me/theorems/4c0e5b35-713c-4a6c-958c-cf55729fd500
-- title:
--   BX: pairing sw
-- statement:
--   The BX construction uses the pairing sw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsPairingValueAddRight.lean#L149-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsPairingValueAddRight.lean#L149-L158

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

theorem ReciprocityTheory.PGsh.BX.pairing_sw (N : ℕ) (x y : B.G R) (z : (R : Type u)ˣ) (h : B.IsPairing N x y z) :
    B.IsPairing N y x z⁻¹ := by sorry
