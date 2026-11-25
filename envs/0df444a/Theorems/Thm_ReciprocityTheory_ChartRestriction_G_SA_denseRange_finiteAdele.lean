-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_denseRange_finiteAdele
-- name    : ReciprocityTheory.ChartRestriction.G.SA.denseRange_finiteAdele
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:33:26.056377+00:00
-- url     : https://prove2.me/theorems/a12b7ce0-60a1-42cb-bf04-25bc61931a72
-- title:
--   SA: dense Range finite Adele
-- statement:
--   The SA construction uses the dense Range finite Adele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/DenseRangeFiniteAdele.lean#L67-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/DenseRangeFiniteAdele.lean#L67-L94

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

theorem ReciprocityTheory.ChartRestriction.G.SA.denseRange_finiteAdele : DenseRange (algebraMap K (FiniteAdeleRing R K)) := by sorry
