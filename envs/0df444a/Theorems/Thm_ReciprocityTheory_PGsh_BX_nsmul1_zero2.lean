-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul1_zero2
-- name    : ReciprocityTheory.PGsh.BX.nsmul1_zero2
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:05:57.707496+00:00
-- url     : https://prove2.me/theorems/09fe2a49-6e1e-42a0-b9bd-29a4535b8c58
-- title:
--   BX: nsmul1 zero2
-- statement:
--   The BX construction uses the nsmul1 zero2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L277-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L277-L285

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

theorem ReciprocityTheory.PGsh.BX.nsmul1_zero2 (x : B.G R) (n : ℕ) : HEq (B.nsmul1 (B.zero2 x) n) (B.zero2 (n • x)) := by sorry
