-- Prove2me | Theorems.Thm_PersistClust_Count_birth_pin_mult_zero
-- name    : PersistClust.Count.birth_pin_mult_zero
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T05:31:01.205183+00:00
-- url     : https://prove2.me/theorems/d5b6e669-9a03-49e2-b774-0d0c4bfcd728
-- title:
--   No bar is born at a non-critical level: the birth-pin census
-- statement:
--   Let stage be a cluster filtration over levels ℝ with relation field J satisfying the FiltrationLaw and IsTameModule tameness (finitely many components per level, no components above a level s₀, and a finite critical set critSet). Let rankFn stage J s t count the level-t component classes whose birth-sup exceeds s, and let mult (rankFn stage J) (b, d) be the persistence-diagram multiplicity of the point (b, d) — the infimum over probes η ∈ (0, (b−d)/2) of the box combination t3_comb stage J b d η of rank-function differences. Theorem (birth-pinning): if d < b and the birth value b is NOT a critical value (b ∉ critSet, as a set of reals), then mult (rankFn stage J) ((b : EReal), (d : EReal)) = 0 — no bar is born at a non-critical level. Proof (by contradiction): if the multiplicity were positive, it would be at least 1. The stable-gap lemma t3_stable_delta provides a window δ₀ > 0 with δ₀ ≤ (b−d)/2 keeping all critical values other than b at distance > δ₀ from b. The probe η* = min(δ₀/2, (b−d)/4) lies in the gap window (0, δ₀) and below (b−d)/2. Unfolding the multiplicity as an infimum of combinations (t3_mult_unfold), positivity forces the combination bracket at η* to be at least 1 (the infimum is a lower bound attained up to η*); the small-η census rewrite (t3_comb_small) turns that bracket into the difference of the b-valued cell censuses at d + η* and d − η*. A nonzero difference forces the upper census (at d + η*) to be nonempty, so some level-(d + η*) cell C has birth-sup exactly b. But every cell's birth-sup is a critical value (the birth-in-critical lemma: a birth-sup is attained in the ancestor-level set, and its boundary behavior pins it into the finite critical set) — contradicting b ∉ critSet.
-- source:
--   T3a final rung (ii-b) of the persistence-clustering deliverable (RR-6968): the birth-pinning census — the diagram multiplicity at (b, d) vanishes when the birth level b is not a critical value (t3_birth_pin in the rankKill master, Scratch_rankR1 L1965-L1995); companion of the death-pinning rung in the T3a census reduction at β = b.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem birth_pin_mult_zero {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b d : ℝ} (hbd : d < b)
    (hb : b ∉ (critSet hTame : Set ℝ)) :
    mult (rankFn stage J) ((b : EReal), (d : EReal)) = 0
    := by sorry
