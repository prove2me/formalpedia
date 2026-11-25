-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PolyMaxLowerBound_chart_margin_fee00aa2a23d
-- name    : P2M_GroundTheory_Heights__Heights_Regular_PolyMaxLowerBound_chart_margin_fee00aa2a23d
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:17:53.222853+00:00
-- url     : https://prove2.me/theorems/367cb9a1-3395-40b4-8531-a23624ac4031
-- title:
--   P2 M Ground Theory Heights  Heights Regular Poly Max Lower Bound chart margin fee00aa2a23d: P2 M Ground Theory Heights  Heights Regular Poly Max Lower Bound chart margin fee00aa2a23d
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Poly Max Lower Bound chart margin fee00aa2a23d construction uses the P2 M Ground Theory Heights  Heights Regular Poly Max Lower Bound chart margin fee00aa2a23d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PPolyMaxLowerBound.lean#L20-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PPolyMaxLowerBound.lean#L20-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PPolyMaxLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Set
open ReciprocityTheory.AnForm.A (polyMax coordDiv limsupExt)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_PolyMaxLowerBound_chart_margin_fee00aa2a23d {X : Type} [TopologicalSpace X] [CompactSpace X] {D : ℕ}
    {A : FinHolAtlas D X} (R : RegChartData A) (j : Fin R.N) :
    ∃ δ Q : ℝ, 0 < δ ∧ 0 ≤ Q ∧ ∀ x ∈ R.mid j, ∀ y ∈ closedBall (R.chart j x) δ,
      y ∈ (R.chart j).target ∧ |R.q j y| ≤ Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«PolyMaxLowerBound».«chart_margin» := P2M_GroundTheory_Heights__Heights_Regular_PolyMaxLowerBound_chart_margin_fee00aa2a23d
