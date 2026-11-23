-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul1_zero1
-- name    : ReciprocityTheory.PGsh.BX.nsmul1_zero1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:08.806814+00:00
-- url     : https://prove2.me/theorems/e3d03199-9593-4cf9-b618-18bac9e4a5f4
-- title:
--   BX: nsmul1 zero1
-- statement:
--   The BX construction uses the nsmul1 zero1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L287-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L287-L291

import Definitions.Def_ReciprocityTheory_DualLattices_SqZeroOfSpan
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
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

theorem ReciprocityTheory.PGsh.BX.nsmul1_zero1 (y : B.G R) (n : ℕ) : HEq (B.nsmul1 (B.zero1 y) n) (B.zero1 y) := by sorry
