-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul_comm
-- name    : ReciprocityTheory.PGsh.BX.nsmul_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:00.296273+00:00
-- url     : https://prove2.me/theorems/19130500-b433-4ed1-9c86-5570f63a7faf
-- title:
--   BX: nsmul comm
-- statement:
--   The BX construction uses the nsmul comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L335-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L335-L342

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

theorem ReciprocityTheory.PGsh.BX.nsmul_comm {x y : B.G R} (u : B.P R x y) (m n : ℕ) :
    B.nsmul2 (B.nsmul1 u m) n = B.nsmul1 (B.nsmul2 u n) m := by sorry
