-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_span_locAtIntPrime_iff_e313f3a4de34
-- name    : P2M_GroundTheory_Heights__Heights_mem_span_locAtIntPrime_iff_e313f3a4de34
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:42:01.884467+00:00
-- url     : https://prove2.me/theorems/0bd9d473-477e-5813-b857-bf6151c99c6a
-- title:
--   P2 M Ground Theory Heights  Heights mem span loc At Int Prime iff e313f3a4de34: P2 M Ground Theory Heights  Heights mem span loc At Int Prime iff e313f3a4de34
-- statement:
--   The P2 M Ground Theory Heights  Heights mem span loc At Int Prime iff e313f3a4de34 construction uses the P2 M Ground Theory Heights  Heights mem span loc At Int Prime iff e313f3a4de34 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L75-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L75-L109

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsGluing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_LocallyFreeSpreadHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_AddBlockPullbackOfChartBundlePullback
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
open ReciprocityTheory.ChartRestriction.G.Geo
variable {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_mem_span_locAtIntPrime_iff_e313f3a4de34 [CharZero Ω] {p : ℕ} (hp : p.Prime) (A : Subalgebra ℤ Ω)
    {E : Type} [AddCommGroup E] [Module Ω E] (L' : AddSubgroup E)
    (hL' : ∀ a ∈ A, ∀ e ∈ L', a • e ∈ L') (e : E) :
    e ∈ Submodule.span (locAtIntPrime p A.toSubring) (L' : Set E) ↔
      ∃ s : ℕ, ¬ p ∣ s ∧ (s : Ω) • e ∈ L' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_span_locAtIntPrime_iff» := P2M_GroundTheory_Heights__Heights_mem_span_locAtIntPrime_iff_e313f3a4de34
