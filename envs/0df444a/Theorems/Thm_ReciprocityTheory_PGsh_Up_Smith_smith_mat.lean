-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_smith_mat
-- name    : ReciprocityTheory.PGsh.Up.Smith.smith_mat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:47.142964+00:00
-- url     : https://prove2.me/theorems/5b807600-251b-41b5-80be-39c57f03c0be
-- title:
--   Smith: smith mat
-- statement:
--   The Smith construction uses the smith mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/BlockOneMulMulBlockOne.lean#L106-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/BlockOneMulMulBlockOne.lean#L106-L177

import Definitions.Def_ReciprocityTheory_DualLattices_UpSmith
import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.Smith
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem ReciprocityTheory.PGsh.Up.Smith.smith_mat (hv : v.Integers R) : ∀ (d n : ℕ) (A : Matrix (Fin d) (Fin n) R),
    ∃ (P : Matrix (Fin d) (Fin d) R) (Q : Matrix (Fin n) (Fin n) R) (a : Fin d → R),
      IsUnit P.det ∧ IsUnit Q.det ∧ ∀ j k, (P * A * Q) j k = if (k : ℕ) = (j : ℕ) then a j else 0
  := by sorry
