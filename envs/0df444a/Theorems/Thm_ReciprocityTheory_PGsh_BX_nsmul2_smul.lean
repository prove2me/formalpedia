-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul2_smul
-- name    : ReciprocityTheory.PGsh.BX.nsmul2_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:22.547451+00:00
-- url     : https://prove2.me/theorems/00124335-bb76-49d2-ac2d-b3351c7a5986
-- title:
--   BX: nsmul2 smul
-- statement:
--   The BX construction uses the nsmul2 smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L306-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L306-L311

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

theorem ReciprocityTheory.PGsh.BX.nsmul2_smul {x y : B.G R} (l : (R : Type u)ˣ) (u : B.P R x y) (n : ℕ) :
    B.nsmul2 (B.smul l u) n = B.smul (l ^ n) (B.nsmul2 u n) := by sorry
