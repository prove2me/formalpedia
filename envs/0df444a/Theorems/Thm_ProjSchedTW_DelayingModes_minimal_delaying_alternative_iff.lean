-- Prove2me | Theorems.Thm_ProjSchedTW_DelayingModes_minimal_delaying_alternative_iff
-- name    : ProjSchedTW.DelayingModes.minimal_delaying_alternative_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T22:40:56.762623+00:00
-- url     : https://prove2.me/theorems/7bdd46e5-ce3c-49e6-8866-629f586b8643
-- title:
--   §2.5.1, Eqs. (2.5.2)–(2.5.3) — characterization of minimal delaying alternatives
-- statement:
--   Let $F$ be a forbidden set of a project and $B\subseteq V$. Then the following are equivalent:
--
--   1. $B$ is a minimal delaying alternative for $F$;
--   2. $B\subseteq F$ and $F\setminus B$ is a maximal feasible subset of $F$ (no feasible $A$ with $F\setminus B\subsetneq A\subseteq F$ exists);
--   3. $B\subseteq F$ and
--   $$\sum_{i\in F\setminus B}r_{ik}\le R_k\quad\text{for all }k\in\mathcal R,\qquad(2.5.2)$$
--   $$\text{for every } j\in B \text{ there is } k\in\mathcal R \text{ with }\sum_{i\in F\setminus B}r_{ik}+r_{jk}>R_k.\qquad(2.5.3)$$
--
--   Condition (2.5.2) says that $B$ is a delaying alternative; (2.5.3) says that putting back any single activity of $B$ makes the set forbidden. The characterization turns the minimality test into $|B|\cdot|\mathcal R|$ inequality checks and is what the recursive procedure of Algorithm 2.5.2 evaluates.
--
--   **Formalization Note.** Maximality of $F\setminus B$ is taken among the feasible subsets of $F$ (Mathlib's `Maximal`), which is the sense in which the page uses it. The standing assumptions of the model are hypotheses.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 46, §2.5.1, Eqs. (2.5.2)–(2.5.3)

import Mathlib
import Definitions.Def_ProjSchedTW_DelayingModes_Project

namespace ProjSchedTW.DelayingModes

theorem minimal_delaying_alternative_iff {n : ℕ} {K : Type} [Fintype K] (P : Project n K)
    (hP : P.StandingAssumptions) (F B : Finset (Fin (n + 2))) (hF : P.IsForbidden F) :
    (P.IsMinimalDelayingAlternative F B ↔
        B ⊆ F ∧ Maximal (fun A : Finset (Fin (n + 2)) => A ⊆ F ∧ P.IsFeasibleSet A) (F \ B)) ∧
      (P.IsMinimalDelayingAlternative F B ↔
        B ⊆ F ∧ (∀ k : K, ∑ i ∈ F \ B, P.r i k ≤ P.R k) ∧
          (∀ j ∈ B, ∃ k : K, P.R k < ∑ i ∈ F \ B, P.r i k + P.r j k)) := by sorry

end ProjSchedTW.DelayingModes
