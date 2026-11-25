-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodChartDim_linForm_single__ee52f128aff3
-- name    : P2M_GroundTheory_Heights__Heights_GoodChartDim_linForm_single__ee52f128aff3
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:26:25.731609+00:00
-- url     : https://prove2.me/theorems/e1916a0d-4a17-4cc5-ac0f-a5df86e3931c
-- title:
--   P2 M Ground Theory Heights  Heights Good Chart Dim lin Form single  ee52f128aff3: P2 M Ground Theory Heights  Heights Good Chart Dim lin Form single  ee52f128aff3
-- statement:
--   The P2 M Ground Theory Heights  Heights Good Chart Dim lin Form single  ee52f128aff3 construction uses the P2 M Ground Theory Heights  Heights Good Chart Dim lin Form single  ee52f128aff3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartDim.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartDim.lean#L54-L56

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

theorem P2M_GroundTheory_Heights__Heights_GoodChartDim_linForm_single__ee52f128aff3 {m : ℕ} (a : Fin m) : linForm (Pi.single a (1 : ℂ)) = X a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GoodChartDim».«linForm_single'» := P2M_GroundTheory_Heights__Heights_GoodChartDim_linForm_single__ee52f128aff3
