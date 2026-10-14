-- Prove2me | Theorems.Thm_PersistClust_Count_death_pin_mult_zero
-- name    : PersistClust.Count.death_pin_mult_zero
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T05:28:36.49834+00:00
-- url     : https://prove2.me/theorems/7e89ce76-cde1-4299-b967-39fc167fbb0b
-- title:
--   No bar dies at a non-critical level: the death-pin census
-- statement:
--   Let stage be a cluster filtration over levels ℝ with relation field J satisfying the FiltrationLaw and IsTameModule tameness (finitely many components per level, no components above a level s₀, and a finite critical set critSet). Let rankFn stage J s t count the level-t component classes whose birth-sup exceeds s, and let mult (rankFn stage J) (b, d) be the persistence-diagram multiplicity of the point (b, d) — the infimum over probes η ∈ (0, (b−d)/2) of the box combination t3_comb stage J b d η of rank-function differences. Theorem (death-pinning): if d < b and the death level d is NOT a critical value (d ∉ critSet, as a set of reals), then mult (rankFn stage J) ((b : EReal), (d : EReal)) = 0 — no essential bar dies at a non-critical level. Proof: the stable-gap lemma t3_stable_delta provides a window δ₀ > 0 with δ₀ ≤ (b−d)/2 around b and d free of other critical values. The half-window probe η = δ₀/2 lies in the gap, and the closed window [d − δ₀/2, d + δ₀/2] contains no critical value at all (hd rules out d itself; every other critical τ is δ₀-far from d). The thread-transport lemma t3_selfTrans then shows the two b-valued cell censuses at the window's ends coincide — descending from d + δ₀/2 to d − δ₀/2 never merges or splits a b-valued cell on a critical-free window, so the counted sets are in bijection and their encards are equal. The multiplicity unfolds (t3_mult_unfold) into an infimum of combinations; evaluating at η = δ₀/2 and rewriting the combination as the census difference (t3_comb_small) gives the difference of two equal counts, which is zero; the infimum is bounded below by 0 and above by this zero value, hence is 0.
-- source:
--   T3a final rung (ii-a) of the persistence-clustering deliverable (RR-6968): the death-pinning census — the diagram multiplicity at (b, d) vanishes when the death level d is not a critical value (t3_death_pin in the rankKill master, Scratch_rankR1 L1936-L1962); cornerstone of the T3a census reduction at β = b.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem death_pin_mult_zero {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b d : ℝ} (hbd : d < b)
    (hd : d ∉ (critSet hTame : Set ℝ)) :
    mult (rankFn stage J) ((b : EReal), (d : EReal)) = 0
    := by sorry
