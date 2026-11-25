-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ChartSectionNotMem_aeval_C_mk_50295ae9d596
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ChartSectionNotMem_aeval_C_mk_50295ae9d596
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:28:19.512452+00:00
-- url     : https://prove2.me/theorems/de474de5-5700-4ff2-aa8a-8d7640c7b486
-- title:
--   P2 M Ground Theory Heights  Heights Targets Chart Section Not Mem aeval C mk 50295ae9d596: P2 M Ground Theory Heights  Heights Targets Chart Section Not Mem aeval C mk 50295ae9d596
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Chart Section Not Mem aeval C mk 50295ae9d596 construction uses the P2 M Ground Theory Heights  Heights Targets Chart Section Not Mem aeval C mk 50295ae9d596 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PChartSectionNotMem.lean#L29-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PChartSectionNotMem.lean#L29-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothMetricOfIsSmoothHerm
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PChartSectionNotMem
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial Algebra
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsSectionOn mcPts segre)
open GroundTheory.Heights₂.Heights.Targets.ChartSectionNotMem
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_ChartSectionNotMem_aeval_C_mk_50295ae9d596 (𝔮 : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (f : MvPolynomial (Σ k, ι k) ℂ) :
    aeval (fun q => (C (Ideal.Quotient.mk 𝔮 (X q)) : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))) f =
      C (Ideal.Quotient.mk 𝔮 f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ChartSectionNotMem».«aeval_C_mk» := P2M_GroundTheory_Heights__Heights_Targets_ChartSectionNotMem_aeval_C_mk_50295ae9d596
