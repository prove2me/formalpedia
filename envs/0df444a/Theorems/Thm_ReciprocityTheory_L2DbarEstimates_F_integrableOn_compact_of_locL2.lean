-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_integrableOn_compact_of_locL2
-- name    : ReciprocityTheory.L2DbarEstimates.F.integrableOn_compact_of_locL2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:30:49.145+00:00
-- url     : https://prove2.me/theorems/03459639-ec48-4055-8b0e-3257f972548a
-- title:
--   F: integrable On compact of loc L2
-- statement:
--   The F construction uses the integrable On compact of loc L2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/IntegrableOnCompactOfLocL2.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/IntegrableOnCompactOfLocL2.lean#L20-L25

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_IntegrableOnCompactOfLocL2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.F.integrableOn_compact_of_locL2 {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (μ : Measure M) [IsFiniteMeasureOnCompacts μ] (u : M → ℂ) (hu : LocalL2Isometry μ u)
    (K : Set M) (hK : IsCompact K) : IntegrableOn u K μ := by sorry
