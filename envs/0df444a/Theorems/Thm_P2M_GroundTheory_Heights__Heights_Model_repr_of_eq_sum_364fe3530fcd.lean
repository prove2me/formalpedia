-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_repr_of_eq_sum_364fe3530fcd
-- name    : P2M_GroundTheory_Heights__Heights_Model_repr_of_eq_sum_364fe3530fcd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:39:42.979364+00:00
-- url     : https://prove2.me/theorems/25a05976-91c8-506f-9359-be7d10dfbe0d
-- title:
--   P2 M Ground Theory Heights  Heights Model repr of eq sum 364fe3530fcd: P2 M Ground Theory Heights  Heights Model repr of eq sum 364fe3530fcd
-- statement:
--   The P2 M Ground Theory Heights  Heights Model repr of eq sum 364fe3530fcd construction uses the P2 M Ground Theory Heights  Heights Model repr of eq sum 364fe3530fcd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueFrameP.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueFrameP.lean#L9-L14

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueFrame
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueFrameP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_Model_repr_of_eq_sum_364fe3530fcd {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}
    {b : Fin r → E} (hli : LinearIndependent Ω b)
    (hsp : Submodule.span Ω (Set.range b) = ⊤) {e : E} {a : Fin r → Ω} (hae : e = ∑ q, a q • b q)
    (q : Fin r) : (Module.Basis.mk hli hsp.ge).repr e q = a q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«repr_of_eq_sum» := P2M_GroundTheory_Heights__Heights_Model_repr_of_eq_sum_364fe3530fcd
