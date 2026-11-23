-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_sw_zero1
-- name    : ReciprocityTheory.PGsh.BX.sw_zero1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:03.591023+00:00
-- url     : https://prove2.me/theorems/e4bff794-b41e-49e5-a7f1-99b99dc0a2fc
-- title:
--   BX: sw zero1
-- statement:
--   The BX construction uses the sw zero1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L255-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L255-L262

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

theorem ReciprocityTheory.PGsh.BX.sw_zero1 (y : B.G R) : B.sw (B.zero1 y) = B.zero2 y := by sorry
