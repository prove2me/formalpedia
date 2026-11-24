-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartDetRatio_detE_sum_a71ef09db231
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ChartDetRatio_detE_sum_a71ef09db231
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:27:24.19068+00:00
-- url     : https://prove2.me/theorems/c04a5b25-3d95-48d2-84b8-9d170961e40d
-- title:
--   P2 M Ground Theory Heights  Heights Inter Chart Det Ratio det E sum a71ef09db231: P2 M Ground Theory Heights  Heights Inter Chart Det Ratio det E sum a71ef09db231
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Chart Det Ratio det E sum a71ef09db231 construction uses the P2 M Ground Theory Heights  Heights Inter Chart Det Ratio det E sum a71ef09db231 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartDetRatio.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartDetRatio.lean#L22-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartDetRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartDetRatio
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Inter_ChartDetRatio_detE_sum_a71ef09db231 {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
    (e : Module.Basis (Fin 2) Ω E) (b : Fin 2 → E) (a a' : Fin 2 → Ω) :
    T.detE e (∑ q, a q • b q) (∑ q, a' q • b q) = (a 0 * a' 1 - a 1 * a' 0) * T.detE e (b 0) (b 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ChartDetRatio».«detE_sum» := P2M_GroundTheory_Heights__Heights_Inter_ChartDetRatio_detE_sum_a71ef09db231
