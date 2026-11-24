-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_Ik_le_one_c5e9977958ee
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_Ik_le_one_c5e9977958ee
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:20.164809+00:00
-- url     : https://prove2.me/theorems/c8d92f7c-d4ce-4103-b1d5-fb5642bcfd2b
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus Ik le one c5e9977958ee: P2 M Ground Theory Heights  Heights Reg Lelong Annulus Ik le one c5e9977958ee
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus Ik le one c5e9977958ee construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus Ik le one c5e9977958ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L279-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L279-L282

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_Ik_le_one_c5e9977958ee (e k : ℕ) : Ik e k ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«Ik_le_one» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_Ik_le_one_c5e9977958ee
