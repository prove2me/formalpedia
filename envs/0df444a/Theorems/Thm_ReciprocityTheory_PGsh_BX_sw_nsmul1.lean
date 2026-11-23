-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_sw_nsmul1
-- name    : ReciprocityTheory.PGsh.BX.sw_nsmul1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:31.793344+00:00
-- url     : https://prove2.me/theorems/ad3725ea-3188-4301-9e5e-d0fed51fd78b
-- title:
--   BX: sw nsmul1
-- statement:
--   The BX construction uses the sw nsmul1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L347-L351
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L347-L351

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

theorem ReciprocityTheory.PGsh.BX.sw_nsmul1 {x y : B.G R} (u : B.P R x y) (n : ℕ) :
    B.sw (B.nsmul1 u n) = B.nsmul2 (B.sw u) n := by sorry
