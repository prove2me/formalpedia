-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_pk_pow_le_Ik_fbb0273b26eb
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_pk_pow_le_Ik_fbb0273b26eb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:12.295365+00:00
-- url     : https://prove2.me/theorems/226aced1-c493-4b2b-b3b0-0cf62f59287a
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus pk pow le Ik fbb0273b26eb: P2 M Ground Theory Heights  Heights Reg Lelong Annulus pk pow le Ik fbb0273b26eb
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus pk pow le Ik fbb0273b26eb construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus pk pow le Ik fbb0273b26eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L284-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L284-L296

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_pk_pow_le_Ik_fbb0273b26eb (e k : ℕ) : pk k ^ (e + 1) ≤ Ik e k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«pk_pow_le_Ik» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_pk_pow_le_Ik_fbb0273b26eb
