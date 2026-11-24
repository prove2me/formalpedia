-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integral_kernel_6618981a4f14
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integral_kernel_6618981a4f14
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:38.327642+00:00
-- url     : https://prove2.me/theorems/43e481e0-ee25-4045-b842-34b78c81bed6
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus integral kernel 6618981a4f14: P2 M Ground Theory Heights  Heights Reg Lelong Annulus integral kernel 6618981a4f14
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus integral kernel 6618981a4f14 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus integral kernel 6618981a4f14 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L264-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L264-L266

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integral_kernel_6618981a4f14 (e : ℕ) (t : ℝ) :
    ∫ w in (0 : ℝ)..t, 1 * (((e + 1 : ℕ) : ℝ) * w ^ (e + 1 - 1)) = t ^ (e + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«integral_kernel» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integral_kernel_6618981a4f14
