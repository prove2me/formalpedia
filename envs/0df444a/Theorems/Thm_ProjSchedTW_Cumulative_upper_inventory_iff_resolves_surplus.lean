-- Prove2me | Theorems.Thm_ProjSchedTW_Cumulative_upper_inventory_iff_resolves_surplus
-- name    : ProjSchedTW.Cumulative.upper_inventory_iff_resolves_surplus
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T00:01:48.185981+00:00
-- url     : https://prove2.me/theorems/a7bf1af5-98a4-464b-9f4d-6ea6a4415ca1
-- title:
--   Theorem 2.12.4 (a) — no inventory excess at any t ≥ 0 iff every minimal surplus set is resolved
-- statement:
--   Consider a project with discrete cumulative resources as in §2.12.1 satisfying (2.12.1), $\underline R_k\le\sum_{i\in V}r_{ik}\le\overline R_k$, and Remark 2.12.2, $\underline R_k\le 0\le\overline R_k$, for every resource $k$. Let $\mathcal F_k^+$ be the set of minimal $k$-surplus sets. For every schedule $S$,
--   $$
--   r_k(S,t)\le\overline R_k\ \ \forall k,\ \forall t\ge 0 \iff \forall k,\ \forall F\in\mathcal F_k^+\ \exists j\in F,\ i\notin F:\ r_{jk}>0,\ r_{ik}<0,\ S_j+p_j\ge S_i .
--   $$
--
--   This is the surplus half of Theorem 2.12.4, as the book's proof establishes it: an inventory excess at some time yields a minimal surplus set violating condition (a), and a minimal surplus set violating (a) yields an excess.
--
--   **Formalization Note** Inventory constraints are required for all $t\ge 0$.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, pp. 132–134, Theorem 2.12.4 (a) and the corresponding part of its proof

import Mathlib
import Definitions.Def_ProjSchedTW_Cumulative_Model

namespace ProjSchedTW.Cumulative

/-- Theorem 2.12.4, part (a) with its half of the proof: the upper inventory constraints hold
for all `t ≥ 0` iff condition (a) holds. -/
theorem upper_inventory_iff_resolves_surplus {n : ℕ} {K : Type} (P : CumulativeProject n K)
    (h2121 : TotalDemandWithinBounds P) (hRem : BoundsStraddleZero P)
    (S : Fin (n + 2) → ℝ) (hS : IsSchedule S) :
    (∀ k : K, ∀ t : ℝ, 0 ≤ t → inventory P S k t ≤ P.Rup k) ↔ ResolvesSurplusSets P S := by sorry

end ProjSchedTW.Cumulative
