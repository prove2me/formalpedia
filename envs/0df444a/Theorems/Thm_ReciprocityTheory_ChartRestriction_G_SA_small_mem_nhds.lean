-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_small_mem_nhds
-- name    : ReciprocityTheory.ChartRestriction.G.SA.small_mem_nhds
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:34:53.823911+00:00
-- url     : https://prove2.me/theorems/dc362eab-30a3-47d1-80dc-a326e4fd8218
-- title:
--   SA: small mem nhds
-- statement:
--   The SA construction uses the small mem nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/DenseRangeFiniteAdele.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/DenseRangeFiniteAdele.lean#L11-L22

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

theorem ReciprocityTheory.ChartRestriction.G.SA.small_mem_nhds (v : HeightOneSpectrum R) {s : Set (v.adicCompletion K)}
    (hs : s ∈ 𝓝 (0 : v.adicCompletion K)) :
    ∃ n : ℕ, ∀ x, Valued.v x ≤ exp (-(n : ℤ)) → x ∈ s := by sorry
