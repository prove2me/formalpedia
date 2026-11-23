-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_exists_orbit_bound
-- name    : ReciprocityTheory.ChartRestriction.DS.exists_orbit_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:42.038525+00:00
-- url     : https://prove2.me/theorems/fc812856-bd81-4d0f-a8ff-6962145d3c6a
-- title:
--   DS: exists orbit bound
-- statement:
--   The DS construction uses the exists orbit bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Analytic.lean#L21-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Analytic.lean#L21-L56

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Unitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Taylor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Series
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Growth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_NcBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Analytic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem ReciprocityTheory.ChartRestriction.DS.exists_orbit_bound (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V) {c : ℝ}
    (hc : ∀ v ∈ V, casimir E v = (c : ℂ) • v) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inP ε X) {v : D} (hv : v ∈ genSub E V) :
    ∃ a : ℕ → ℝ, (∀ m, ‖((((actM E X) ^ m) v : D) : H)‖ ≤ a m) ∧ (∀ m, 0 ≤ a m) ∧
      ∀ r : ℝ, 0 ≤ r → r * (√2 * √(∑ a, ∑ b, ‖X a b‖ ^ 2)) < 1 →
        Summable fun m : ℕ => a m * r ^ m / (m.factorial : ℝ) := by sorry
