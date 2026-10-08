-- Prove2me | Theorems.Thm_ProjSchedTW_DelayingModes_two_element_forbidden_set_precedence
-- name    : ProjSchedTW.DelayingModes.two_element_forbidden_set_precedence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T23:05:29.68178+00:00
-- url     : https://prove2.me/theorems/9f0abe1f-d651-40aa-9382-acd60575b975
-- title:
--   Theorem 2.5.11 — preprocessing of two-element forbidden sets
-- statement:
--   Let $UB\in\mathbb Z$ be an upper bound on the project duration and let $d_{ij}$ denote the longest path lengths in the temporal scheduling network $N^+$ with the backward arc weight $\delta_{n+1,0}=-UB$. Let $\{i,j\}$ be a two-element forbidden set ($i\ne j$ and $r_{ik}+r_{jk}>R_k$ for some $k$) with
--   $$d_{ij}<p_i\quad\text{and}\quad d_{ij}>-p_j.$$
--   Then every feasible schedule $S$ with $S_{n+1}\le UB$ satisfies
--   $$S_j\ge S_i+p_i.$$
--
--   The theorem justifies adding the precedence constraint $i\to j$ before the enumeration starts: when the time windows leave room for $i$ and $j$ to overlap but not for $j$ to precede $i$, every feasible schedule within the bound must let $i$ precede $j$. Case (a) of p. 54, $LS_i<ES_j+p_j$, is contained in it.
--
--   **Formalization Note.** Distances take values in `WithBot ℝ` ($-\infty$ as `⊥`) and are maxima over simple paths of $N^+$. $UB$ is an integer, like all time lags of the book. The standing assumptions of the model are hypotheses; resource constraints are required for all $t\ge0$.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 55, Theorem 2.5.11 (network N+ with δ_{n+1,0} = −UB from p. 54)

import Mathlib
import Definitions.Def_ProjSchedTW_DelayingModes_Project
import Definitions.Def_ProjSchedTW_DelayingModes_Distance

namespace ProjSchedTW.DelayingModes

theorem two_element_forbidden_set_precedence {n : ℕ} {K : Type} [Fintype K] (P : Project n K)
    (hP : P.StandingAssumptions) (UB : ℤ) (i j : Fin (n + 2)) (hij : i ≠ j)
    (hF : P.IsForbidden {i, j})
    (hlt : P.distPlus UB i j < (((P.p i : ℝ)) : WithBot ℝ))
    (hgt : ((-(P.p j : ℝ) : ℝ) : WithBot ℝ) < P.distPlus UB i j)
    (S : Fin (n + 2) → ℝ) (hS : P.IsFeasible S) (hUB : S (Fin.last (n + 1)) ≤ UB) :
    S i + P.p i ≤ S j := by sorry

end ProjSchedTW.DelayingModes
