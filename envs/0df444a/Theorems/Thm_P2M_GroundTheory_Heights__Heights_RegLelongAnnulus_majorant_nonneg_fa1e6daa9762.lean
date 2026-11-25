-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_majorant_nonneg_fa1e6daa9762
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_majorant_nonneg_fa1e6daa9762
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:17:20.336868+00:00
-- url     : https://prove2.me/theorems/671b16db-645c-4591-8d37-978348d78f3d
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus majorant nonneg fa1e6daa9762: P2 M Ground Theory Heights  Heights Reg Lelong Annulus majorant nonneg fa1e6daa9762
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus majorant nonneg fa1e6daa9762 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus majorant nonneg fa1e6daa9762 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L359-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L359-L359

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_majorant_nonneg_fa1e6daa9762 (s : ℝ) (z : Fin n → ℂ) : 0 ≤ majorant x s z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«majorant_nonneg» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_majorant_nonneg_fa1e6daa9762
