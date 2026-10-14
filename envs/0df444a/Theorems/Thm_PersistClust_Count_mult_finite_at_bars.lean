-- Prove2me | Theorems.Thm_PersistClust_Count_mult_finite_at_bars
-- name    : PersistClust.Count.mult_finite_at_bars
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T09:44:30.814519+00:00
-- url     : https://prove2.me/theorems/98612917-2d36-4c10-806a-0f97835bf7bb
-- title:
--   The multiplicity diagram is finite at every bar: mult(rankFn)(p) ≠ ⊤
-- statement:
--   Let ι be a type, stage : ℝ → Set ι a stage family and J : ℝ → ι → ι → Prop a relation family satisfying the filtration law hLaw and the tameness module axioms hTame. Then for every point p of the extended-real plane with second coordinate equal to ⊥ (a birth-only bar) or strictly below the first coordinate (a genuine bar d < b), the multiplicity is finite: mult (rankFn stage J) p ≠ ⊤. Proof: a general exclusion principle says that any extended natural bounded by a finite one is finite (x ≤ y, y ≠ ⊤ ⟹ x ≠ ⊤). If p.1 is a real coercion and p.2 = ⊥, the multiplicity unfolds to an infimum over ε > 0 and t ≤ b − ε of rank differences; evaluating at ε = 1 and t = b − 1 bounds it by rankFn (b − 1) (b − 1) − rankFn (b + 1) (b − 1) ≤ rankFn (b − 1) (b − 1), which is finite by q-tameness (every rank is finite: the t-classes of points alive at s form a finite set). If p.2 < p.1, both coordinates are real coercions, and evaluating the infimum at ε = (b − d)/4 bounds the multiplicity by a finite rank, again finite by q-tameness. If p.1 is not a real coercion (⊥ or ⊤), the multiplicity is 0 by the unfolding's if-branch, and 0 ≠ ⊤.
-- source:
--   Support theorem of the persistence-clustering deliverable (RR-6968, Theorem 4.6 cluster): T3a-iii (t3_mult_lt_top in the rankKill master, Scratch_rankR1 L2050-2101, with inlined helper t2_qtame L595-609) — the barwise finiteness of the multiplicity diagram consumed by the finite-support thread-identity and elder-rule transfer of the matching-census assembly.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem mult_finite_at_bars {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) (p : EReal × EReal)
    (hp : p.2 = ⊥ ∨ p.2 < p.1) : mult (rankFn stage J) p ≠ ⊤
    := by sorry
