-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_mem_spanCols_iff
-- name    : ReciprocityTheory.PGsh.L2.mem_spanCols_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:16.242171+00:00
-- url     : https://prove2.me/theorems/801ef553-e439-41d1-9ae5-c90ba064db7f
-- title:
--   L2: mem span Cols iff
-- statement:
--   The L2 construction uses the mem span Cols iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationDetEqOfSpanEq.lean#L12-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationDetEqOfSpanEq.lean#L12-L24

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

theorem ReciprocityTheory.PGsh.L2.mem_spanCols_iff (B : Matrix X X C) (f : X → C) :
    f ∈ Submodule.span R (Set.range fun j x => B x j) ↔ ∃ w ∈ intFun (C := C) R X, f = B *ᵥ w := by sorry
