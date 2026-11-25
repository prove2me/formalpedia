-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_norm_orbit_sub_partial_le
-- name    : ReciprocityTheory.ChartRestriction.DS.norm_orbit_sub_partial_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:58:12.221966+00:00
-- url     : https://prove2.me/theorems/6a0dfe82-3d77-45b8-ba0d-476bf02f9805
-- title:
--   DS: norm orbit sub partial le
-- statement:
--   The DS construction uses the norm orbit sub partial le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Taylor.lean#L37-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Taylor.lean#L37-L91

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_IteratedDerivOrbit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Taylor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Filter Topology
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem ReciprocityTheory.ChartRestriction.DS.norm_orbit_sub_partial_le (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v : D) (a : ℕ → ℝ)
    (ha : ∀ m, ‖((((actM E X) ^ m) v : D) : H)‖ ≤ a m) (t₀ t : ℝ) (N : ℕ) :
    ‖σ (NormedSpace.exp ((t : ℂ) • X)) (v : H) - ∑ m ∈ range (N + 1),
        (((t - t₀) ^ m / (m.factorial : ℝ) : ℝ) : ℂ) •
          σ (NormedSpace.exp ((t₀ : ℂ) • X)) ((((actM E X) ^ m) v : D) : H)‖ ≤
      a (N + 1) * |t - t₀| ^ (N + 1) / ((N + 1).factorial : ℝ) := by sorry
