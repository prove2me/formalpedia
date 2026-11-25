-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_nhds_zero_int
-- name    : ReciprocityTheory.ChartRestriction.G.SA.nhds_zero_int
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:34:05.50568+00:00
-- url     : https://prove2.me/theorems/ab9edf76-0d90-4864-986b-b1cc953276a4
-- title:
--   SA: nhds zero int
-- statement:
--   The SA construction uses the nhds zero int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/DenseRangeFiniteAdele.lean#L24-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/DenseRangeFiniteAdele.lean#L24-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_AdeleApproximation_AdeleIntA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_DenseRangeFiniteAdele
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology WithZero Filter
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem ReciprocityTheory.ChartRestriction.G.SA.nhds_zero_int {N : Set (FiniteAdeleRing R K)} (hN : N ∈ 𝓝 (0 : FiniteAdeleRing R K)) :
    ∃ r : R, r ≠ 0 ∧ ∀ y : FiniteAdeleRing R K,
      (∀ v, Valued.v (y v) ≤ v.intValuation r) → y ∈ N := by sorry
