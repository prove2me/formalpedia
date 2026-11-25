-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_fibreSnd_nsmul_smul
-- name    : ReciprocityTheory.PGsh.BX.fibreSnd_nsmul_smul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:05:36.782156+00:00
-- url     : https://prove2.me/theorems/61c7c628-72b6-4b3d-b18c-d9742db7f09c
-- title:
--   BX: fibre Snd nsmul smul
-- statement:
--   The BX construction uses the fibre Snd nsmul smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L192-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L192-L196

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

theorem ReciprocityTheory.PGsh.BX.fibreSnd_nsmul_smul {x : B.G R} (l : (R : Type u)ˣ) (a : B.S2 R x) (n : ℕ) :
    n • B.SecondaryComponentScale l a = B.SecondaryComponentScale (l ^ n) (n • a) := by sorry
