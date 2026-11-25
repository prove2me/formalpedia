-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_ringEquiv_mem_nonZeroDivisors
-- name    : ReciprocityTheory.AnForm.R.ringEquiv_mem_nonZeroDivisors
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:30:18.602326+00:00
-- url     : https://prove2.me/theorems/7c1de02b-2f7b-59ae-aed6-5e89c27ab3b3
-- title:
--   R: ring Equiv mem non Zero Divisors
-- statement:
--   The R construction uses the ring Equiv mem non Zero Divisors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsB.lean#L58-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsB.lean#L58-L64

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section

theorem ReciprocityTheory.AnForm.R.ringEquiv_mem_nonZeroDivisors {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) {a : A}
    (ha : a ∈ nonZeroDivisors A) : e a ∈ nonZeroDivisors B := by sorry
