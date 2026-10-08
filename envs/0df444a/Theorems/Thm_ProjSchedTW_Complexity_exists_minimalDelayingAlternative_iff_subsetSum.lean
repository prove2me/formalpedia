-- Prove2me | Theorems.Thm_ProjSchedTW_Complexity_exists_minimalDelayingAlternative_iff_subsetSum
-- name    : ProjSchedTW.Complexity.exists_minimalDelayingAlternative_iff_subsetSum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T02:09:58.51024+00:00
-- url     : https://prove2.me/theorems/b6013b02-ee56-4f67-9e8c-98201f0f507f
-- title:
--   Proof of Proposition 2.5.4 — with r_{j*} = 1, a minimal delaying alternative contains j* iff some A ⊆ F∖{j*} sums to R
-- statement:
--   Consider a single renewable resource with capacity $R\in\mathbb N$ and requirements $r_i\in\mathbb N$. Let $F$ be a set of activities and $j^*\in F$ with $r_{j^*}=1$. Then there is a minimal delaying alternative $B$ for $F$ with $j^*\in B$ if and only if there is a set $A\subseteq F\setminus\{j^*\}$ with
--   $$\sum_{i\in A}r_i=R.$$
--
--   This is the core of the reduction from SUBSET SUM in the proof of Proposition 2.5.4: an instance with sizes $s(i)$ and threshold $M$ becomes $F=\mathcal I\cup\{j^*\}$, $r_i=s(i)$, $r_{j^*}=1$, $R=M$.
--
--   **Formalization Note** The single resource is `Fin 1`, written as index `0`. Requirements are natural numbers and may be zero; the equivalence holds without assuming $r_i\ge1$ for $i\ne j^*$, and without assuming that $F$ is forbidden (if it is not, both sides are false).
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 48, proof of Proposition 2.5.4 ("Hence, there is a minimal delaying alternative B containing j* exactly if there is a set A ⊆ F∖{j*} with Σ_{i∈A} r_i = R")

import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_DelayingAlternatives

namespace ProjSchedTW.Complexity

/-- Proof of Proposition 2.5.4 (p. 48), single resource with `r_{j*} = 1`: some minimal
delaying alternative for `F` contains `j*` iff some `A ⊆ F \ {j*}` has `∑_{i ∈ A} r_i = R`. -/
theorem exists_minimalDelayingAlternative_iff_subsetSum {n : ℕ} (r : Fin (n + 2) → Fin 1 → ℕ)
    (R : Fin 1 → ℕ) (F : Finset (Fin (n + 2))) (jstar : Fin (n + 2)) (hjF : jstar ∈ F)
    (hr : r jstar 0 = 1) :
    (∃ B, IsMinimalDelayingAlternative r R F B ∧ jstar ∈ B) ↔
      ∃ A ⊆ F.erase jstar, ∑ i ∈ A, r i 0 = R 0 := by sorry

end ProjSchedTW.Complexity
