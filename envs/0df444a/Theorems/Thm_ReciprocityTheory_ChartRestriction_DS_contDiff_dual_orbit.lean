-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_contDiff_dual_orbit
-- name    : ReciprocityTheory.ChartRestriction.DS.contDiff_dual_orbit
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:51:32.366825+00:00
-- url     : https://prove2.me/theorems/995c401f-72af-5a86-a0e7-69cbca8ed504
-- title:
--   DS: cont Diff dual orbit
-- statement:
--   The DS construction uses the cont Diff dual orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Taylor.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Taylor.lean#L32-L35

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

theorem ReciprocityTheory.ChartRestriction.DS.contDiff_dual_orbit (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (φ : H →L[ℝ] ℝ) (w : D) (N : ℕ) :
    ContDiff ℝ N (fun s : ℝ => φ (σ (NormedSpace.exp ((s : ℂ) • X)) (w : H))) := by sorry
