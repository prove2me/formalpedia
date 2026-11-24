-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_mid_subset_source_96b409876f03
-- name    : P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_mid_subset_source_96b409876f03
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:05.726802+00:00
-- url     : https://prove2.me/theorems/81541954-7910-4241-baa3-902855bf118d
-- title:
--   P2 M Ground Theory Heights  Heights Regular Potential Charts mid subset source 96b409876f03: P2 M Ground Theory Heights  Heights Regular Potential Charts mid subset source 96b409876f03
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Potential Charts mid subset source 96b409876f03 construction uses the P2 M Ground Theory Heights  Heights Regular Potential Charts mid subset source 96b409876f03 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/Statements.lean#L65-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/Statements.lean#L65-L66

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory Metric Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli coordDiv limsupExt regMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsCompatChart)
open ReciprocityTheory.AnForm (levi)
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.PotentialCharts
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (P : PotentialCharts A)

theorem P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_mid_subset_source_96b409876f03 (j : Fin P.N) : P.mid j ⊆ (P.chart j).source := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«PotentialCharts».«mid_subset_source» := P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_mid_subset_source_96b409876f03
