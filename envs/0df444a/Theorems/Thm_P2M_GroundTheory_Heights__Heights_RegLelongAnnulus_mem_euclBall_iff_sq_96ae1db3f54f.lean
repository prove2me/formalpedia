-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_mem_euclBall_iff_sq_96ae1db3f54f
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_mem_euclBall_iff_sq_96ae1db3f54f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:29:26.670513+00:00
-- url     : https://prove2.me/theorems/99eea164-9dcb-4955-99d3-197724619b07
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus mem eucl Ball iff sq 96ae1db3f54f: P2 M Ground Theory Heights  Heights Reg Lelong Annulus mem eucl Ball iff sq 96ae1db3f54f
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus mem eucl Ball iff sq 96ae1db3f54f construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus mem eucl Ball iff sq 96ae1db3f54f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L337-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L337-L339

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_mem_euclBall_iff_sq_96ae1db3f54f {ρ : ℝ} (hρ : 0 < ρ) (z : Fin n → ℂ) :
    z ∈ euclBall x ρ ↔ euclPot (z - x) < ρ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«mem_euclBall_iff_sq» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_mem_euclBall_iff_sq_96ae1db3f54f
