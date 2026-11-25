-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_algebraMap_mem_nonZeroDivisors_of_isLocalization
-- name    : ReciprocityTheory.AnForm.R.algebraMap_mem_nonZeroDivisors_of_isLocalization
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:30:39.178589+00:00
-- url     : https://prove2.me/theorems/d38a8c92-884a-5c30-b531-7b852a044904
-- title:
--   R: algebra Map mem non Zero Divisors of is Localization
-- statement:
--   The R construction uses the algebra Map mem non Zero Divisors of is Localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsB.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsB.lean#L9-L18

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

theorem ReciprocityTheory.AnForm.R.algebraMap_mem_nonZeroDivisors_of_isLocalization {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] {a : R} (ha : a ∈ nonZeroDivisors R) :
    algebraMap R S a ∈ nonZeroDivisors S := by sorry
