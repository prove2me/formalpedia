-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_hasSum_orbit_of_bound
-- name    : ReciprocityTheory.ChartRestriction.DS.hasSum_orbit_of_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:57:24.578171+00:00
-- url     : https://prove2.me/theorems/4afe4971-08ee-4b8e-abad-0d8023a8d938
-- title:
--   DS: has Sum orbit of bound
-- statement:
--   The DS construction uses the has Sum orbit of bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Taylor.lean#L93-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Taylor.lean#L93-L117

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

theorem ReciprocityTheory.ChartRestriction.DS.hasSum_orbit_of_bound (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v : D) (a : ℕ → ℝ)
    (ha : ∀ m, ‖((((actM E X) ^ m) v : D) : H)‖ ≤ a m) (t₀ t : ℝ)
    (hs : Summable fun m : ℕ => a m * |t - t₀| ^ m / (m.factorial : ℝ)) :
    HasSum (fun m : ℕ => (((t - t₀) ^ m / (m.factorial : ℝ) : ℝ) : ℂ) •
        σ (NormedSpace.exp ((t₀ : ℂ) • X)) ((((actM E X) ^ m) v : D) : H))
      (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) := by sorry
