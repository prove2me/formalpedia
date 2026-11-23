-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_pmap_nsmul1
-- name    : ReciprocityTheory.PGsh.BX.pmap_nsmul1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:08.6541+00:00
-- url     : https://prove2.me/theorems/a5ec77eb-bf7b-4e2d-9c63-22ebe82052a5
-- title:
--   BX: pmap nsmul1
-- statement:
--   The BX construction uses the pmap nsmul1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L144-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L144-L151

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

theorem ReciprocityTheory.PGsh.BX.pmap_nsmul1 {S : LAlg R₀} (f : LHom R S) {x y : B.G R} (u : B.P R x y) (n : ℕ) :
    HEq (B.pmap f (B.nsmul1 u n)) (B.nsmul1 (B.pmap f u) n) := by sorry
