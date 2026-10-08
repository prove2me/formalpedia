-- Prove2me | Theorems.Thm_ProjSchedTW_Complexity_minimalDelayingAlternative_iff_single
-- name    : ProjSchedTW.Complexity.minimalDelayingAlternative_iff_single
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T02:09:55.604985+00:00
-- url     : https://prove2.me/theorems/405e877a-3fe9-4dde-a127-849787c3d181
-- title:
--   Proof of Proposition 2.5.4 — with one resource, B is a minimal delaying alternative iff R − min_B r_j < Σ_{F∖B} r_i ≤ R
-- statement:
--   Consider a single renewable resource with capacity $R\in\mathbb N$ and requirements $r_i\in\mathbb N$. Let $F$ be a set of activities, $B\subseteq F$ and $j^*\in B$. Then $B$ is a minimal delaying alternative for $F$ if and only if
--   $$R-\min_{j\in B}r_j\ <\ \sum_{i\in F\setminus B}r_i\ \le\ R.$$
--
--   In the proof of Proposition 2.5.4 this characterization turns the search for a minimal delaying alternative containing $j^*$ into a subset-sum question.
--
--   **Formalization Note** The single resource is `Fin 1`, written as index `0`. The minimum is `Finset.inf'` over the nonempty set $B$ (nonempty because $j^*\in B$), and the inequalities are evaluated in $\mathbb Z$ so that $R-\min_B r_j$ is not truncated. The hypothesis $B\subseteq F$ is implicit in the book (a delaying alternative for $F$ is a subset of $F$).
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 48, proof of Proposition 2.5.4 ("Then B is a minimal delaying alternative if and only if R − min_{j∈B} r_j < Σ_{i∈F∖B} r_i ≤ R")

import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_DelayingAlternatives

namespace ProjSchedTW.Complexity

/-- Proof of Proposition 2.5.4 (p. 48), single resource: for `j* ∈ B ⊆ F`, `B` is a minimal
delaying alternative for `F` iff `R − min_{j ∈ B} r_j < ∑_{i ∈ F \ B} r_i ≤ R`. -/
theorem minimalDelayingAlternative_iff_single {n : ℕ} (r : Fin (n + 2) → Fin 1 → ℕ)
    (R : Fin 1 → ℕ) (F B : Finset (Fin (n + 2))) (jstar : Fin (n + 2)) (hBF : B ⊆ F)
    (hj : jstar ∈ B) :
    IsMinimalDelayingAlternative r R F B ↔
      ((R 0 : ℤ) - B.inf' ⟨jstar, hj⟩ (fun j => (r j 0 : ℤ)) < ∑ i ∈ F \ B, (r i 0 : ℤ) ∧
        ∑ i ∈ F \ B, (r i 0 : ℤ) ≤ (R 0 : ℤ)) := by sorry

end ProjSchedTW.Complexity
