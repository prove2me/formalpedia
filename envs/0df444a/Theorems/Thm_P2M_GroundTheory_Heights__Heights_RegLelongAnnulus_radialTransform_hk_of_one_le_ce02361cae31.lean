-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_hk_of_one_le_ce02361cae31
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_hk_of_one_le_ce02361cae31
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:55.7064+00:00
-- url     : https://prove2.me/theorems/448f1632-be0b-46f5-9847-c33afcf512f6
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus radial Transform hk of one le ce02361cae31: P2 M Ground Theory Heights  Heights Reg Lelong Annulus radial Transform hk of one le ce02361cae31
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus radial Transform hk of one le ce02361cae31 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus radial Transform hk of one le ce02361cae31 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L259-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L259-L262

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_hk_of_one_le_ce02361cae31 (e k : ℕ) {v : ℝ} (hv : 1 ≤ v) :
    radialTransform (e + 1) (hk k) v = -Ik e k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«radialTransform_hk_of_one_le» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_hk_of_one_le_ce02361cae31
