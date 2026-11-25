-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_exists_matrix_span_eq
-- name    : ReciprocityTheory.PGsh.L2.exists_matrix_span_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:05:40.398915+00:00
-- url     : https://prove2.me/theorems/5879c9f8-66b8-4c67-92e6-8a5b151c2098
-- title:
--   L2: exists matrix span eq
-- statement:
--   The L2 construction uses the exists matrix span eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsUnitDetOfSpanEq.lean#L59-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsUnitDetOfSpanEq.lean#L59-L136

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}

theorem ReciprocityTheory.PGsh.L2.exists_matrix_span_eq (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    (M : Submodule R (X → C)) (hfg : M.FG)
    (hsp : Submodule.span C (M : Set (X → C)) = ⊤) :
    ∃ β : Matrix X X C, IsUnit β.det ∧ M = Submodule.span R (Set.range fun j x => β x j) := by sorry
