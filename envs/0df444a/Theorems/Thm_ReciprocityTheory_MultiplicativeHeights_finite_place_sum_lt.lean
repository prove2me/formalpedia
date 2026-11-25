-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_finite_place_sum_lt
-- name    : ReciprocityTheory.MultiplicativeHeights.finite_place_sum_lt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:22.369796+00:00
-- url     : https://prove2.me/theorems/a9d12463-2e04-556e-8495-9699eddf6a07
-- title:
--   Multiplicative Heights: finite place sum lt
-- statement:
--   The Multiplicative Heights construction uses the finite place sum lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussAbsMulOfMonomialOrder.lean#L48-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussAbsMulOfMonomialOrder.lean#L48-L56

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_Lemmata_GeneralBFactLeftExtra_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open NumberField
variable {K : Type*} [Field K] [NumberField K] {σ : Type*}

theorem ReciprocityTheory.MultiplicativeHeights.finite_place_sum_lt {ι : Type*} (w : FinitePlace K) (t : Finset ι) (a : ι → K) {M : ℝ}
    (hM : 0 < M) (h : ∀ i ∈ t, w (a i) < M) : w (∑ i ∈ t, a i) < M := by sorry
