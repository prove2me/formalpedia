-- Prove2me | Theorems.Thm_ProjSchedTW_Temporal_dist_least_solution
-- name    : ProjSchedTW.Temporal.dist_least_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T14:34:32.752007+00:00
-- url     : https://prove2.me/theorems/2f8a7a31-ae31-4f88-89ab-b35be54549d2
-- title:
--   §1.3, Eq. (1.3.3) — the distances are the least solution of the arc bounds and the triangle inequality
-- statement:
--   Let a project with AoN network $N$ be given, let $L\in\mathbb Z$, and suppose the temporal scheduling network $N^+$ (with backward arc $\langle n+1,0\rangle$ of weight $-L$) contains no cycle of positive length. Let $d_{ij}\in\mathbb Z\cup\{-\infty\}$ be the longest path lengths in $N^+$. Then
--
--   1. $d_{ii}=0$ for all $i\in V$;
--   2. $d_{ij}\ge\delta_{ij}$ for every arc $\langle i,j\rangle\in E^+$;
--   3. the triangle inequality holds:
--   $$d_{ij}\ \ge\ d_{ih}+d_{hj}\qquad(h,i,j\in V);\qquad(1.3.3)$$
--   4. $d$ is the smallest such family: every $D:V\times V\to\mathbb Z\cup\{-\infty\}$ with $D_{ii}=0$, $D_{ij}\ge\delta_{ij}$ on $E^+$ and $D_{ij}\ge D_{ih}+D_{hj}$ satisfies $d_{ij}\le D_{ij}$ for all $i,j$.
--
--   This characterization is what makes longest path lengths computable by label-correcting and triple algorithms, and it is used throughout the book to reason about the distance matrix.
--
--   **Formalization Note.** Sums in $\mathbb Z\cup\{-\infty\}$ follow $-\infty+x=-\infty$. The book fixes $d_{ii}=0$ by convention, so the competing families $D$ are required to satisfy $D_{ii}=0$ as well.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, §1.3, p. 11, Eq. (1.3.3)

import Mathlib
import Definitions.Def_ProjSchedTW_Temporal_Project

namespace ProjSchedTW.Temporal

/-- §1.3, p. 11, Eq. (1.3.3): if the temporal scheduling network `N⁺` has no cycle of positive
length, its distances `d_ij` (with `d_ii = 0`) satisfy `d_ij ≥ δ_ij` on the arcs of `N⁺` and
the triangle inequality, and they are the smallest values doing so. -/
theorem dist_least_solution {n : ℕ} (P : Project n) (L : ℤ)
    (hL : ¬ HasPositiveCycle (P.N.plus L)) :
    (∀ i, dist (P.N.plus L) i i = 0) ∧
    (∀ e ∈ (P.N.plus L).E,
      ((P.N.plus L).δ e.1 e.2 : WithBot ℤ) ≤ dist (P.N.plus L) e.1 e.2) ∧
    (∀ h i j, dist (P.N.plus L) i h + dist (P.N.plus L) h j ≤ dist (P.N.plus L) i j) ∧
    (∀ D : Fin (n + 2) → Fin (n + 2) → WithBot ℤ,
      (∀ i, D i i = 0) →
      (∀ e ∈ (P.N.plus L).E, ((P.N.plus L).δ e.1 e.2 : WithBot ℤ) ≤ D e.1 e.2) →
      (∀ h i j, D i h + D h j ≤ D i j) →
      ∀ i j, dist (P.N.plus L) i j ≤ D i j) := by sorry

end ProjSchedTW.Temporal
