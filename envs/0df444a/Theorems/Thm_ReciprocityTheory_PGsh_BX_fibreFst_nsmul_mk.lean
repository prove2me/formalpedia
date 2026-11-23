-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_fibreFst_nsmul_mk
-- name    : ReciprocityTheory.PGsh.BX.fibreFst_nsmul_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:19.460282+00:00
-- url     : https://prove2.me/theorems/64c7192b-e845-4cce-8c69-9d34e7b67317
-- title:
--   BX: fibre Fst nsmul mk
-- statement:
--   The BX construction uses the fibre Fst nsmul mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L108-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L108-L116

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

theorem ReciprocityTheory.PGsh.BX.fibreFst_nsmul_mk {x y : B.G R} (u : B.P R x y) (n : ℕ) :
    (n • (B.S1mk u)) = ⟨n • x, B.nsmul1 u n⟩ := by sorry
