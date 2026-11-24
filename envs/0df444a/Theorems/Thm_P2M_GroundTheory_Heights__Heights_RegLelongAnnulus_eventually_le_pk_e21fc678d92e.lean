-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_eventually_le_pk_e21fc678d92e
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_eventually_le_pk_e21fc678d92e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:51.151215+00:00
-- url     : https://prove2.me/theorems/89fdccd2-7006-43c6-a1b0-7e71d9133326
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus eventually le pk e21fc678d92e: P2 M Ground Theory Heights  Heights Reg Lelong Annulus eventually le pk e21fc678d92e
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus eventually le pk e21fc678d92e construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus eventually le pk e21fc678d92e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L319-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L319-L320

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_eventually_le_pk_e21fc678d92e {v : ℝ} (hv : v < 1) : ∀ᶠ k in atTop, v ≤ pk k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«eventually_le_pk» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_eventually_le_pk_e21fc678d92e
