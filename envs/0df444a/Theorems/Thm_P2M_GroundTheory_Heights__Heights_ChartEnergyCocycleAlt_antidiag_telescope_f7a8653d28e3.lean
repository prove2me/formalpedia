-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_antidiag_telescope_f7a8653d28e3
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_antidiag_telescope_f7a8653d28e3
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:19:04.001234+00:00
-- url     : https://prove2.me/theorems/21431212-3220-4a19-bdb9-2e01e0a36a07
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt antidiag telescope f7a8653d28e3: P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt antidiag telescope f7a8653d28e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt antidiag telescope f7a8653d28e3 construction uses the P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt antidiag telescope f7a8653d28e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyCocycle.lean#L154-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyCocycle.lean#L154-L173

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergyCocycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergySymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyCocycle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory Filter
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartEnergyCocycleAlt
variable {e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_antidiag_telescope_f7a8653d28e3 (g : ℕ → ℕ → ℝ) : ∀ e : ℕ,
    ∑ k ∈ Finset.range (e + 1), ∑ j ∈ Finset.range (e - k), (g (k + 1) j - g k (j + 1)) =
      ∑ k ∈ Finset.range (e + 1), (g k 0 - g 0 k)
  := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergyCocycleAlt».«antidiag_telescope» := P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_antidiag_telescope_f7a8653d28e3
