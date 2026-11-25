-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_h_sum_right
-- name    : ReciprocityTheory.MultiplicativeHeights.approxB_h_sum_right
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:03:49.813041+00:00
-- url     : https://prove2.me/theorems/f2837c63-ecdd-511a-9d6d-09bb73bc77bd
-- title:
--   Multiplicative Heights: approx B h sum right
-- statement:
--   The Multiplicative Heights construction uses the approx B h sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisB.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisB.lean#L33-L36

import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisB
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

theorem ReciprocityTheory.MultiplicativeHeights.approxB_h_sum_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    {α : Type*} (s : Finset α) (x : Fin r → K) (f : α → Fin r → K) :
    S.h x (∑ j ∈ s, f j) = ∑ j ∈ s, S.h x (f j) := by sorry
