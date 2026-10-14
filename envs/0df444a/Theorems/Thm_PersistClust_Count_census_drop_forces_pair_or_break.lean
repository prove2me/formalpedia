-- Prove2me | Theorems.Thm_PersistClust_Count_census_drop_forces_pair_or_break
-- name    : PersistClust.Count.census_drop_forces_pair_or_break
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-13T09:19:00.167448+00:00
-- url     : https://prove2.me/theorems/b4048227-2f88-4dd5-ae50-7a8d1db96ad5
-- title:
--   Census drop forces a same-death pair or a value-break pin (the SLIVER dichotomy)
-- statement:
--   Let a tame 0-dimensional persistence module be given by a filtration law (stage, J), and let (b, d) be a real point with d < b at which the bar multiplicity is nonzero. Let delta0 be a positive window excluding every critical level from b and from d, and let eta be a probe with 0 < eta < delta0 and eta < (b - d)/2. Assume two descent-regularity facts at the probe level d + eta: (hstrict) every component class C whose birth-supremum at d + eta equals b still has birth-supremum exactly b after descending to level d; and (hshare) two distinct such b-valued classes at d + eta descend to distinct classes at d. Then the following dichotomy holds: EITHER there are two DISTINCT component classes M1 and M2 at level d, both of birth-supremum b, whose further descents to level d - eta coincide (a same-death-at-d pair: both threads die together at d), OR some component class M at level d with birth-supremum b has its birth-supremum strictly INCREASE above b when descended to level d - eta (a break-at-d pin: the thread's value breaks upward below d). The mechanism is a pigeonhole census count: the nonzero multiplicity forces the census of b-valued classes at d + eta to strictly exceed that at d - eta (the eta-window census drop, via the combination t3_comb at small eta); the descent-to-d map is injective on the b-valued classes at d + eta by hshare, so it injects the above-census into the d-census; and if neither alternative held, the descent-to-(d - eta) map would be injective on the b-valued d-classes (no shared below-descent) and would land inside the b-valued classes at d - eta (no value break, because birth-suprema only grow under descent), chaining the three cardinalities into |VAL| <= |BELOW'| < |PIN'| <= |VAL| - an impossibility.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the SLIVER dichotomy of the rank-level kill (ORCH M1, Entry 9 of the deathBar rearch v2 lane), extracted from the GREEN text of t5_l1_rankKill as a self-contained leaf. The nonzero bar multiplicity plus the crit-gap window force the eta-window census drop (pin-census exceeds below-census at the probe), and the two descent injections pigeonhole into the disjunction driving the same-death-pair / value-break-pin analyses of the death-side case tree. Companion of the accepted census_back_mult_nonzero (its helper closure), descent_value_cap_at_coincidence, and the rungB descent-family support tools.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem census_drop_forces_pair_or_break {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {b d δ₀ η : ℝ} (hbd : d < b)
    (hgap : (∀ τ ∈ critSet hTame, τ ≠ b → δ₀ < |τ - b|) ∧
      (∀ τ ∈ critSet hTame, τ ≠ d → δ₀ < |τ - d|))
    (hη : η ∈ Set.Ioo (0 : ℝ) δ₀) (hηbd : η < (b - d) / 2)
    (hpx : mult (rankFn stage J) ((b : EReal), (d : EReal)) ≠ 0)
    (hle1 : d ≤ d + η) (hle2 : d - η ≤ d)
    (hstrict : ∀ C : comps stage J (d + η), birthSup hLaw (d + η) C = b →
      birthSup hLaw d (structMap hLaw hle1 C) = b)
    (hshare : ∀ (P1 P2 : comps stage J (d + η)), P1 ≠ P2 →
      birthSup hLaw (d + η) P1 = b → birthSup hLaw (d + η) P2 = b →
      structMap hLaw hle1 P1 ≠ structMap hLaw hle1 P2) :
    (∃ (M₁ M₂ : comps stage J d), birthSup hLaw d M₁ = b ∧
        birthSup hLaw d M₂ = b ∧ M₁ ≠ M₂ ∧
        structMap hLaw hle2 M₁ = structMap hLaw hle2 M₂) ∨
    (∃ M : comps stage J d, birthSup hLaw d M = b ∧
      b < birthSup hLaw (d - η) (structMap hLaw hle2 M))
    := by sorry
