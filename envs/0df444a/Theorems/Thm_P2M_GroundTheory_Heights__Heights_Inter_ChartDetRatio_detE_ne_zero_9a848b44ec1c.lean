-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartDetRatio_detE_ne_zero_9a848b44ec1c
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ChartDetRatio_detE_ne_zero_9a848b44ec1c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:27:41.709954+00:00
-- url     : https://prove2.me/theorems/413f190b-5445-4379-9c57-304f140e2dbf
-- title:
--   P2 M Ground Theory Heights  Heights Inter Chart Det Ratio det E ne zero 9a848b44ec1c: P2 M Ground Theory Heights  Heights Inter Chart Det Ratio det E ne zero 9a848b44ec1c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Chart Det Ratio det E ne zero 9a848b44ec1c construction uses the P2 M Ground Theory Heights  Heights Inter Chart Det Ratio det E ne zero 9a848b44ec1c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartDetRatio.lean#L28-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartDetRatio.lean#L28-L37

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ChartDetRatio_detE_ne_zero_9a848b44ec1c {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
    (e : Module.Basis (Fin 2) Ω E) (b : Fin 2 → E) (hli : LinearIndependent Ω b)
    (hsp : Submodule.span Ω (Set.range b) = ⊤) : T.detE e (b 0) (b 1) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ChartDetRatio».«detE_ne_zero» := P2M_GroundTheory_Heights__Heights_Inter_ChartDetRatio_detE_ne_zero_9a848b44ec1c
