-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_pshShift_local
-- name    : ReciprocityTheory.AnForm.M.pshShift_local
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:33:06.100753+00:00
-- url     : https://prove2.me/theorems/a94bd51d-34ff-4369-942a-e0083f94ba11
-- title:
--   M: psh Shift local
-- statement:
--   The M construction uses the psh Shift local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PshShiftB.lean#L21-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PshShiftB.lean#L21-L78

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Filter Topology FinHolAtlas
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem ReciprocityTheory.AnForm.M.pshShift_local (A : FinHolAtlas e X) (Ω : LocPot X) (hΩ : IsPotential A Ω)
    (hpos : IsPosPot A Ω) (w : X → ℝ) (hw : A.Smooth w) (p : X) (j : Fin A.n)
    (hp : p ∈ (A.chart j).source) :
    ∃ r > 0, ∃ m : ℝ, Metric.closedBall (A.chart j p) r ⊆
        (A.chart j).target ∩ (A.chart j).symm ⁻¹' Ω.U p ∧
      ∀ y ∈ Metric.closedBall (A.chart j p) r, ∀ u : Fin e → ℂ,
        m * levi (Ω.φ p ∘ (A.chart j).symm) y u ≤ levi (w ∘ (A.chart j).symm) y u := by sorry
