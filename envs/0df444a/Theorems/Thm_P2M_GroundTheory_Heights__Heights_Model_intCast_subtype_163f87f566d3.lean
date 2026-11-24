-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_intCast_subtype_163f87f566d3
-- name    : P2M_GroundTheory_Heights__Heights_Model_intCast_subtype_163f87f566d3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:30.138797+00:00
-- url     : https://prove2.me/theorems/cb604330-f21c-4657-b77c-e8941a04a731
-- title:
--   P2 M Ground Theory Heights  Heights Model int Cast subtype 163f87f566d3: P2 M Ground Theory Heights  Heights Model int Cast subtype 163f87f566d3
-- statement:
--   The P2 M Ground Theory Heights  Heights Model int Cast subtype 163f87f566d3 construction uses the P2 M Ground Theory Heights  Heights Model int Cast subtype 163f87f566d3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueFrame.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueFrame.lean#L43-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueFrame
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
variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]

theorem P2M_GroundTheory_Heights__Heights_Model_intCast_subtype_163f87f566d3 (A : Subalgebra ℤ Ω) (z : ℤ) :
    (⟨(z : Ω), intCast_mem A z⟩ : A) = (z : A) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«intCast_subtype» := P2M_GroundTheory_Heights__Heights_Model_intCast_subtype_163f87f566d3
