-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_pairing_mul
-- name    : ReciprocityTheory.PGsh.BX.pairing_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:22.820947+00:00
-- url     : https://prove2.me/theorems/f9d32e19-f674-4f3e-8052-48ba3c6a9c4e
-- title:
--   BX: pairing mul
-- statement:
--   The BX construction uses the pairing mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsPairingValueAddRight.lean#L256-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsPairingValueAddRight.lean#L256-L299

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

theorem ReciprocityTheory.PGsh.BX.pairing_mul (N p : ℕ) (x y : B.G R) (z : (R : Type u)ˣ) (hx : N • x = 0)
    (hy : (N * p) • y = 0) (h : B.IsPairing (N * p) x y z) : B.IsPairing N x (p • y) z := by sorry
