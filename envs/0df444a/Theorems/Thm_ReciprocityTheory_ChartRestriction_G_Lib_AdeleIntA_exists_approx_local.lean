-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Lib_AdeleIntA_exists_approx_local
-- name    : ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA.exists_approx_local
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:31:04.222804+00:00
-- url     : https://prove2.me/theorems/33694d8e-1b4e-438b-8c81-21ab876a13a0
-- title:
--   Adele Int A: exists approx local
-- statement:
--   The Adele Int A construction uses the exists approx local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/AdeleApproximation/AdeleIntA.lean#L92-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/AdeleApproximation/AdeleIntA.lean#L92-L123

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_AdeleApproximation_AdeleIntA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Lib ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA.exists_approx_local (v : HeightOneSpectrum R) (c : v.adicCompletion K)
    (hc : c ∈ v.adicCompletionIntegers K) (r : R) (hr : r ≠ 0) :
    ∃ a : R, Valued.v (c - algebraMap K _ (algebraMap R K a)) ≤ v.intValuation r := by sorry
