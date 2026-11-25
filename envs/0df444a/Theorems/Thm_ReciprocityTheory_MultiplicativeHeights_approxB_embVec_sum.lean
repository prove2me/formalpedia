-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_embVec_sum
-- name    : ReciprocityTheory.MultiplicativeHeights.approxB_embVec_sum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:02:54.527915+00:00
-- url     : https://prove2.me/theorems/27862c5c-462f-5e74-a3a5-c75c2e8f8218
-- title:
--   Multiplicative Heights: approx B emb Vec sum
-- statement:
--   The Multiplicative Heights construction uses the approx B emb Vec sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisB.lean#L73-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisB.lean#L73-L76

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

theorem ReciprocityTheory.MultiplicativeHeights.approxB_embVec_sum {K : Type} [Field K] [NumberField K] {r : ℕ} (σ : K →+* ℂ)
    {α : Type*} (s : Finset α) (f : α → Fin r → K) :
    embVec σ (∑ j ∈ s, f j) = ∑ j ∈ s, embVec σ (f j) := by sorry
