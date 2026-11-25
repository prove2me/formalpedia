-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_VerticalDegreeAfterAdjoining_chart_congr_8f517aba47f5
-- name    : P2M_GroundTheory_Heights__Heights_Inter_VerticalDegreeAfterAdjoining_chart_congr_8f517aba47f5
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:24:57.728436+00:00
-- url     : https://prove2.me/theorems/e25de6a9-ffeb-44ab-a6cc-1e0db25ac7af
-- title:
--   P2 M Ground Theory Heights  Heights Inter Vertical Degree After Adjoining chart congr 8f517aba47f5: P2 M Ground Theory Heights  Heights Inter Vertical Degree After Adjoining chart congr 8f517aba47f5
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Vertical Degree After Adjoining chart congr 8f517aba47f5 construction uses the P2 M Ground Theory Heights  Heights Inter Vertical Degree After Adjoining chart congr 8f517aba47f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ChartCongr.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ChartCongr.lean#L17-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherSide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiProjPrimeImageZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRankAdjoinFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFnDegAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartScalingIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StAdjoinIndepRelfinrank
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFinrankAdjoinRange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ChartCongr
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem P2M_GroundTheory_Heights__Heights_Inter_VerticalDegreeAfterAdjoining_chart_congr_8f517aba47f5 {K' Ω : Type*} {ι' : K' → Type*} (x' : (Σ k', ι' k') → Ω)
    (i' : ∀ k', ι' k') {a b : K'} (h : a = b) : x' ⟨a, i' a⟩ = x' ⟨b, i' b⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«VerticalDegreeAfterAdjoining».«chart_congr» := P2M_GroundTheory_Heights__Heights_Inter_VerticalDegreeAfterAdjoining_chart_congr_8f517aba47f5
