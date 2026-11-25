-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_det_le_of_posSemidef
-- name    : ReciprocityTheory.MultiplicativeHeights.approxB_det_le_of_posSemidef
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:03:22.625935+00:00
-- url     : https://prove2.me/theorems/9d198efc-956b-52d2-a70c-f90254fbb711
-- title:
--   Multiplicative Heights: approx B det le of pos Semidef
-- statement:
--   The Multiplicative Heights construction uses the approx B det le of pos Semidef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisA.lean#L178-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisA.lean#L178-L213

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem ReciprocityTheory.MultiplicativeHeights.approxB_det_le_of_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n ℂ) (hN : N.PosSemidef)
    (c : ℝ) (hc : ∀ k, (N k k).re ≤ c) : ‖N.det‖ ≤ c ^ Fintype.card n := by sorry
