-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_orbit_hasSum_taylor
-- name    : ReciprocityTheory.ChartRestriction.DS.orbit_hasSum_taylor
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:59:29.6989+00:00
-- url     : https://prove2.me/theorems/7e69f6ec-8d8c-5ef7-af13-d9b748673d8c
-- title:
--   DS: orbit has Sum taylor
-- statement:
--   The DS construction uses the orbit has Sum taylor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Analytic.lean#L58-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Analytic.lean#L58-L67

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

theorem ReciprocityTheory.ChartRestriction.DS.orbit_hasSum_taylor (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V) {c : ℝ}
    (hc : ∀ v ∈ V, casimir E v = (c : ℂ) • v) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inP ε X) {v : D} (hv : v ∈ genSub E V) (t₀ t : ℝ)
    (ht : |t - t₀| * (√2 * √(∑ a, ∑ b, ‖X a b‖ ^ 2)) < 1) :
    HasSum (fun m : ℕ => (((t - t₀) ^ m / (m.factorial : ℝ) : ℝ) : ℂ) •
        σ (NormedSpace.exp ((t₀ : ℂ) • X)) ((((actM E X) ^ m) v : D) : H))
      (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) := by sorry
