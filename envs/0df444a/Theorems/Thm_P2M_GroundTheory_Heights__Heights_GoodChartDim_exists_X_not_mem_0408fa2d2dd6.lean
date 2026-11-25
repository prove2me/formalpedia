-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodChartDim_exists_X_not_mem_0408fa2d2dd6
-- name    : P2M_GroundTheory_Heights__Heights_GoodChartDim_exists_X_not_mem_0408fa2d2dd6
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:24:11.446267+00:00
-- url     : https://prove2.me/theorems/1dc69371-9e44-40cc-9271-07b237d3aa19
-- title:
--   P2 M Ground Theory Heights  Heights Good Chart Dim exists X not mem 0408fa2d2dd6: P2 M Ground Theory Heights  Heights Good Chart Dim exists X not mem 0408fa2d2dd6
-- statement:
--   The P2 M Ground Theory Heights  Heights Good Chart Dim exists X not mem 0408fa2d2dd6 construction uses the P2 M Ground Theory Heights  Heights Good Chart Dim exists X not mem 0408fa2d2dd6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartDim.lean#L80-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartDim.lean#L80-L84

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

theorem P2M_GroundTheory_Heights__Heights_GoodChartDim_exists_X_not_mem_0408fa2d2dd6 {m : ℕ} {W : Ideal (MvPolynomial (Fin m) ℂ)} {t : Fin m → ℂ} (h : linForm t ∉ W) :
    ∃ a, X a ∉ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GoodChartDim».«exists_X_not_mem» := P2M_GroundTheory_Heights__Heights_GoodChartDim_exists_X_not_mem_0408fa2d2dd6
