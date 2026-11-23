-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_castFst_heq
-- name    : ReciprocityTheory.PGsh.BX.castFst_heq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:10.371032+00:00
-- url     : https://prove2.me/theorems/5ff10cad-ce00-4158-bc99-17814122954a
-- title:
--   BX: cast Fst heq
-- statement:
--   The BX construction uses the cast Fst heq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L35-L36

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

theorem ReciprocityTheory.PGsh.BX.castFst_heq {x x' y : B.G R} (h : x = x') (u : B.P R x y) : HEq (B.tr1 h u) u := by sorry
