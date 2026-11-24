-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mem_ideal_of_sum_10ad4e89fd6e
-- name    : P2M_GroundTheory_Heights__Heights_Model_mem_ideal_of_sum_10ad4e89fd6e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:47.823016+00:00
-- url     : https://prove2.me/theorems/4172aa96-6a27-43de-9df8-59e56bc89cad
-- title:
--   P2 M Ground Theory Heights  Heights Model mem ideal of sum 10ad4e89fd6e: P2 M Ground Theory Heights  Heights Model mem ideal of sum 10ad4e89fd6e
-- statement:
--   The P2 M Ground Theory Heights  Heights Model mem ideal of sum 10ad4e89fd6e construction uses the P2 M Ground Theory Heights  Heights Model mem ideal of sum 10ad4e89fd6e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueFrame.lean#L36-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueFrame.lean#L36-L41

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

theorem P2M_GroundTheory_Heights__Heights_Model_mem_ideal_of_sum_10ad4e89fd6e {A : Subalgebra ℤ Ω} (Q : Ideal A) {k : ℕ} (a y : Fin k → Ω)
    (ha : ∀ l, a l ∈ A) (hy : ∀ l, y l ∈ A) (hyQ : ∀ l, (⟨y l, hy l⟩ : A) ∈ Q) {z : Ω}
    (hz : z ∈ A) (hsum : ∑ l, a l * y l = z) : (⟨z, hz⟩ : A) ∈ Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«mem_ideal_of_sum» := P2M_GroundTheory_Heights__Heights_Model_mem_ideal_of_sum_10ad4e89fd6e
