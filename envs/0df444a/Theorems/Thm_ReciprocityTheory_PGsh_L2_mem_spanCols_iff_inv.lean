-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_mem_spanCols_iff_inv
-- name    : ReciprocityTheory.PGsh.L2.mem_spanCols_iff_inv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:05:44.861524+00:00
-- url     : https://prove2.me/theorems/65704b28-97b0-4ee9-beda-2833c3b29a37
-- title:
--   L2: mem span Cols iff inv
-- statement:
--   The L2 construction uses the mem span Cols iff inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationDetEqOfSpanEq.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationDetEqOfSpanEq.lean#L26-L33

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetEqOfSpanEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {X : Type} [Fintype X] [DecidableEq X]

theorem ReciprocityTheory.PGsh.L2.mem_spanCols_iff_inv (B : Matrix X X C) (hB : IsUnit B.det) (f : X → C) :
    f ∈ Submodule.span R (Set.range fun j x => B x j) ↔ B⁻¹ *ᵥ f ∈ intFun (C := C) R X := by sorry
