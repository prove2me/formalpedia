-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_mem_nonZeroDivisors_of_bijective
-- name    : ReciprocityTheory.AnForm.R.mem_nonZeroDivisors_of_bijective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:55:44.096876+00:00
-- url     : https://prove2.me/theorems/956d62b8-5f4a-4fae-ad9f-73a4ba14800a
-- title:
--   R: mem non Zero Divisors of bijective
-- statement:
--   The R construction uses the mem non Zero Divisors of bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsA.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsA.lean#L9-L16

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjBCompl
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section

theorem ReciprocityTheory.AnForm.R.mem_nonZeroDivisors_of_bijective {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hb : Function.Bijective φ) {a : R} (ha : a ∈ nonZeroDivisors R) : φ a ∈ nonZeroDivisors S := by sorry
