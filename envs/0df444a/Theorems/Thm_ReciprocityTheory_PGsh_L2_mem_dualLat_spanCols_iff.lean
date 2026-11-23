-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_mem_dualLat_spanCols_iff
-- name    : ReciprocityTheory.PGsh.L2.mem_dualLat_spanCols_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:22.350917+00:00
-- url     : https://prove2.me/theorems/18da832a-72e8-4613-a09d-4d8b45a7af6d
-- title:
--   L2: mem dual Lat span Cols iff
-- statement:
--   The L2 construction uses the mem dual Lat span Cols iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationDetEqOfSpanEq.lean#L35-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationDetEqOfSpanEq.lean#L35-L50

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

theorem ReciprocityTheory.PGsh.L2.mem_dualLat_spanCols_iff (B : Matrix X X C) (u : X → C) :
    u ∈ dualLat (Submodule.span R (Set.range fun j x => B x j)) ↔ u ᵥ* B ∈ intFun (C := C) R X := by sorry
