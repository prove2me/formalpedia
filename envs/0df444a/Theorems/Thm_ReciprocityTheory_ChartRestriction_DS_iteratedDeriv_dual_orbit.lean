-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_iteratedDeriv_dual_orbit
-- name    : ReciprocityTheory.ChartRestriction.DS.iteratedDeriv_dual_orbit
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:50:48.590047+00:00
-- url     : https://prove2.me/theorems/6f4b64d5-64da-43a2-a031-2843fbf54c51
-- title:
--   DS: iterated Deriv dual orbit
-- statement:
--   The DS construction uses the iterated Deriv dual orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Taylor.lean#L17-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Taylor.lean#L17-L30

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

theorem ReciprocityTheory.ChartRestriction.DS.iteratedDeriv_dual_orbit (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (φ : H →L[ℝ] ℝ) (m : ℕ) : ∀ w : D,
    iteratedDeriv m (fun s : ℝ => φ (σ (NormedSpace.exp ((s : ℂ) • X)) (w : H))) =
      fun s : ℝ => φ (σ (NormedSpace.exp ((s : ℂ) • X)) ((((actM E X) ^ m) w : D) : H)) := by sorry
