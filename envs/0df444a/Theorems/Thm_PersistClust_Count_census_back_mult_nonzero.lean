-- Prove2me | Theorems.Thm_PersistClust_Count_census_back_mult_nonzero
-- name    : PersistClust.Count.census_back_mult_nonzero
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-13T08:18:14.814646+00:00
-- url     : https://prove2.me/theorems/32c73413-9f16-4011-b195-92cba5ab9f4b
-- title:
--   Census-back: a thread above v and an empty below-census force a nonzero bar multiplicity at (b, v)
-- statement:
--   For a tame persistence module, let v < b and let δ₀ be positive with δ₀ ≤ (b−v)/2, such that no critical level τ ≠ b lies within δ₀ of b and no critical level τ ≠ v lies within δ₀ of v. Suppose that for every probe η in (0, δ₀) there is a component class at level v+η with birth-supremum exactly b (a b-thread alive just above v), while no component class at level v−η has birth-supremum b (the below-census is empty). Then the multiplicity of the point (b, v) in the persistence diagram of the module is nonzero.
-- source:
--   The bar finisher of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster, census lane): the census reading of the box combination turns the thread-above/empty-below census data into a nonzero bar at (b, v). The multiplicity is the infimum of the box combination over small probes; stability makes the combination constant on a window, monotonicity compares probes, and the combination reduces (via the crit-free gaps at b and v) to the number of b-cells above v minus the number of b-cells below v — the first is ≥ 1 by the thread supply, the second is 0 by the empty below-census.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem census_back_mult_nonzero {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {b v δ₀ : ℝ} (hbd : v < b)
    (hδ₀0 : 0 < δ₀) (hδ₀le : δ₀ ≤ (b - v) / 2)
    (hgap : (∀ τ ∈ critSet hTame, τ ≠ b → δ₀ < |τ - b|) ∧
      (∀ τ ∈ critSet hTame, τ ≠ v → δ₀ < |τ - v|))
    (hthr : ∀ η : ℝ, η ∈ Set.Ioo (0 : ℝ) δ₀ →
        ∃ C : comps stage J (v + η), birthSup hLaw (v + η) C = b)
    (hbelow : ∀ η : ℝ, η ∈ Set.Ioo (0 : ℝ) δ₀ →
        ∀ C : comps stage J (v - η), birthSup hLaw (v - η) C ≠ b) :
    mult (rankFn stage J) ((b : EReal), (v : EReal)) ≠ 0
    := by sorry
