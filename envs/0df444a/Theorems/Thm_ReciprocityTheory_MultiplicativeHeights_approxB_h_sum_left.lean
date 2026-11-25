-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_h_sum_left
-- name    : ReciprocityTheory.MultiplicativeHeights.approxB_h_sum_left
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:03:43.196272+00:00
-- url     : https://prove2.me/theorems/583a6e93-4468-40ae-9965-6e40b27a7742
-- title:
--   Multiplicative Heights: approx B h sum left
-- statement:
--   The Multiplicative Heights construction uses the approx B h sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisB.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisB.lean#L53-L56

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

theorem ReciprocityTheory.MultiplicativeHeights.approxB_h_sum_left {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    {α : Type*} (s : Finset α) (y : Fin r → K) (f : α → Fin r → K) :
    S.h (∑ j ∈ s, f j) y = ∑ j ∈ s, S.h (f j) y := by sorry
