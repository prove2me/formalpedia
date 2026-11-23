-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_swap_castFst
-- name    : ReciprocityTheory.PGsh.BX.swap_castFst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:55.731876+00:00
-- url     : https://prove2.me/theorems/0199939f-a362-4ce1-89df-5d62f66bb853
-- title:
--   BX: swap cast Fst
-- statement:
--   The BX construction uses the swap cast Fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L344-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InstAddCommMonoidFibreFst.lean#L344-L345

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

theorem ReciprocityTheory.PGsh.BX.swap_castFst {x x' y : B.G R} (h : x = x') (u : B.P R x y) :
    B.sw (B.tr1 h u) = B.tr2 h (B.sw u) := by sorry
