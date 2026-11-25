-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodChartDim_linForm_sub_one_not_mem_3340afce65b2
-- name    : P2M_GroundTheory_Heights__Heights_GoodChartDim_linForm_sub_one_not_mem_3340afce65b2
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T16:25:11.350154+00:00
-- url     : https://prove2.me/theorems/c2330b7c-81fc-47c3-945f-78a49649ca43
-- title:
--   P2 M Ground Theory Heights  Heights Good Chart Dim lin Form sub one not mem 3340afce65b2: P2 M Ground Theory Heights  Heights Good Chart Dim lin Form sub one not mem 3340afce65b2
-- statement:
--   The P2 M Ground Theory Heights  Heights Good Chart Dim lin Form sub one not mem 3340afce65b2 construction uses the P2 M Ground Theory Heights  Heights Good Chart Dim lin Form sub one not mem 3340afce65b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartDim.lean#L70-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartDim.lean#L70-L78

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

theorem P2M_GroundTheory_Heights__Heights_GoodChartDim_linForm_sub_one_not_mem_3340afce65b2 {m : ℕ} {V : Ideal (MvPolynomial (Fin m) ℂ)} (hV : IsHomogIdeal V) (hne : V ≠ ⊤)
    (t : Fin m → ℂ) : linForm t - 1 ∉ V := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GoodChartDim».«linForm_sub_one_not_mem» := P2M_GroundTheory_Heights__Heights_GoodChartDim_linForm_sub_one_not_mem_3340afce65b2
