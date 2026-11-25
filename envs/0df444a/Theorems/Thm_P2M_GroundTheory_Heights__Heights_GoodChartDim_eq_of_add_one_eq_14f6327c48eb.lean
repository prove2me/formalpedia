-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodChartDim_eq_of_add_one_eq_14f6327c48eb
-- name    : P2M_GroundTheory_Heights__Heights_GoodChartDim_eq_of_add_one_eq_14f6327c48eb
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:26:26.651958+00:00
-- url     : https://prove2.me/theorems/2c080733-1eee-4527-aa9c-191f25700e9b
-- title:
--   P2 M Ground Theory Heights  Heights Good Chart Dim eq of add one eq 14f6327c48eb: P2 M Ground Theory Heights  Heights Good Chart Dim eq of add one eq 14f6327c48eb
-- statement:
--   The P2 M Ground Theory Heights  Heights Good Chart Dim eq of add one eq 14f6327c48eb construction uses the P2 M Ground Theory Heights  Heights Good Chart Dim eq of add one eq 14f6327c48eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartDim.lean#L94-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartDim.lean#L94-L108

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StConeVanishingHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StConeSliceIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartDehomogPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartZeroSet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartHomogenise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartDehomog
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar mcPts segre)
open GroundTheory.Heights₂.Heights.GoodChartDim
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_GoodChartDim_eq_of_add_one_eq_14f6327c48eb {x : WithBot ℕ∞} {e : ℕ} (h : x + 1 = (e : WithBot ℕ∞) + 1) : x = e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GoodChartDim».«eq_of_add_one_eq» := P2M_GroundTheory_Heights__Heights_GoodChartDim_eq_of_add_one_eq_14f6327c48eb
