-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_majorant_one_2d3599a009c6
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_majorant_one_2d3599a009c6
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:16:40.579326+00:00
-- url     : https://prove2.me/theorems/551a790e-b226-4d44-8a5e-af1bc8ff92c6
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus majorant one 2d3599a009c6: P2 M Ground Theory Heights  Heights Reg Lelong Annulus majorant one 2d3599a009c6
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus majorant one 2d3599a009c6 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus majorant one 2d3599a009c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L361-L365
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L361-L365

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.RegLelongAnnulus
variable {n : ℕ} (x : Fin n → ℂ)

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_majorant_one_2d3599a009c6 {s : ℝ} {z : Fin n → ℂ} (hz : euclPot (z - x) ≤ s ^ 2) : majorant x s z = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«majorant_one» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_majorant_one_2d3599a009c6
