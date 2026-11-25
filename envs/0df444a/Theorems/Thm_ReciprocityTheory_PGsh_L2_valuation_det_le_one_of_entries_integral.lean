-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_valuation_det_le_one_of_entries_integral
-- name    : ReciprocityTheory.PGsh.L2.valuation_det_le_one_of_entries_integral
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:06:02.799936+00:00
-- url     : https://prove2.me/theorems/c36ac38e-e4bd-4086-a78a-826a750a5859
-- title:
--   L2: valuation det le one of entries integral
-- statement:
--   The L2 construction uses the valuation det le one of entries integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationDetLeOneOfEntriesIntegral.lean#L116-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationDetLeOneOfEntriesIntegral.lean#L116-L122

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetLeOneOfEntriesIntegral
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
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

theorem ReciprocityTheory.PGsh.L2.valuation_det_le_one_of_entries_integral (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    (M : Matrix X X C) (hM : ∀ i j, ∃ r : R, algebraMap R C r = M i j) : v M.det ≤ 1 := by sorry
