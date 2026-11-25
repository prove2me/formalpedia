-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_isPairingValue_add_left
-- name    : ReciprocityTheory.PGsh.BX.isPairingValue_add_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:13.820627+00:00
-- url     : https://prove2.me/theorems/ab590cf0-1f7b-4347-9e10-4b933552a094
-- title:
--   BX: is Pairing Value add left
-- statement:
--   The BX construction uses the is Pairing Value add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsPairingValueAddRight.lean#L87-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsPairingValueAddRight.lean#L87-L116

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

theorem ReciprocityTheory.PGsh.BX.isPairingValue_add_left (N : ℕ) (x x' y : B.G R) (z z' : (R : Type u)ˣ) (h : B.IsPairing N x y z)
    (h' : B.IsPairing N x' y z') : B.IsPairing N (x + x') y (z * z') := by sorry
