-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_fibreFst_nsmul_smul
-- name    : ReciprocityTheory.PGsh.BX.fibreFst_nsmul_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:05:23.420877+00:00
-- url     : https://prove2.me/theorems/e3b6d7be-20ce-5cf7-8327-a6273c4d7c17
-- title:
--   BX: fibre Fst nsmul smul
-- statement:
--   The BX construction uses the fibre Fst nsmul smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L118-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L118-L122

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

theorem ReciprocityTheory.PGsh.BX.fibreFst_nsmul_smul {y : B.G R} (l : (R : Type u)ˣ) (a : B.S1 R y) (n : ℕ) :
    n • B.PrimaryComponentScale l a = B.PrimaryComponentScale (l ^ n) (n • a) := by sorry
