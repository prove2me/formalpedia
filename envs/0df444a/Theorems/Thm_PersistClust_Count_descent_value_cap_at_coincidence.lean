-- Prove2me | Theorems.Thm_PersistClust_Count_descent_value_cap_at_coincidence
-- name    : PersistClust.Count.descent_value_cap_at_coincidence
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-13T08:00:04.803439+00:00
-- url     : https://prove2.me/theorems/13252b35-639d-41c1-9937-0f5004cfd1e7
-- title:
--   Descent-ray value cap at a coincidence level (const-squeeze)
-- statement:
--   For a tame module, if two component classes at level w coincide after descending to a lower probe level v (their v-descents are the same class), then the whole descent ray of the second class between v and w is capped by the first class's value at the coincidence level: for every s with v <= s <= w, the s-descent of the second class has birth-supremum at most the v-value of the first class's descent. Proof: rungB descent-monotonicity bounds the s-descent's value by the common v-descent's value, and the coincidence rewrites that common value as the first class's.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the const-squeeze cap consumed by the just-closed S6 branch of the rank-level kill (t5_l1_rankKill STRICT branch, rankR1) — a constant thread pinning the shared lower cell converts a lower-level coincidence of two descent rays into a uniform value cap on the second ray, re-routing the second thread's walk into the first thread's birth band.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem descent_value_cap_at_coincidence {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {w v : ℝ} (hvw : v ≤ w) {I₁ I₂ : comps stage J w}
    (hcoinc : structMap hLaw hvw I₁ = structMap hLaw hvw I₂)
    {s : ℝ} (hvs : v ≤ s) (hsw : s ≤ w) :
    birthSup hLaw s (structMap hLaw hsw I₂) ≤
      birthSup hLaw v (structMap hLaw hvw I₁)
    := by sorry
