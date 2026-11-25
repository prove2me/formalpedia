-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_embVec_sub
-- name    : ReciprocityTheory.MultiplicativeHeights.approxB_embVec_sub
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:03:24.877871+00:00
-- url     : https://prove2.me/theorems/ceb7981f-94b8-49ae-9cec-ffe003d8be9e
-- title:
--   Multiplicative Heights: approx B emb Vec sub
-- statement:
--   The Multiplicative Heights construction uses the approx B emb Vec sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisB.lean#L63-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisB.lean#L63-L66

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

theorem ReciprocityTheory.MultiplicativeHeights.approxB_embVec_sub {K : Type} [Field K] [NumberField K] {r : ℕ} (σ : K →+* ℂ)
    (x y : Fin r → K) : embVec σ (x - y) = embVec σ x - embVec σ y := by sorry
