-- Prove2me | Theorems.Thm_ProjSchedTW_Cumulative_lower_inventory_iff_resolves_shortage
-- name    : ProjSchedTW.Cumulative.lower_inventory_iff_resolves_shortage
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T00:02:12.078435+00:00
-- url     : https://prove2.me/theorems/4599f69c-8566-40ca-af7d-884d4870a8d0
-- title:
--   Theorem 2.12.4 (b) — no inventory shortage at any t ≥ 0 iff every minimal shortage set is resolved
-- statement:
--   Consider a project with discrete cumulative resources as in §2.12.1 satisfying (2.12.1), $\underline R_k\le\sum_{i\in V}r_{ik}\le\overline R_k$, and Remark 2.12.2, $\underline R_k\le 0\le\overline R_k$, for every resource $k$. Let $\mathcal F_k^-$ be the set of minimal $k$-shortage sets. For every schedule $S$,
--   $$
--   r_k(S,t)\ge\underline R_k\ \ \forall k,\ \forall t\ge 0 \iff \forall k,\ \forall F\in\mathcal F_k^-\ \exists j\in F,\ i\notin F:\ r_{jk}<0,\ r_{ik}>0,\ S_j\ge S_i+p_i .
--   $$
--
--   This is the shortage half of Theorem 2.12.4, which the book proves "analogously" to the surplus half.
--
--   **Formalization Note** Inventory constraints are required for all $t\ge 0$.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, pp. 132–134, Theorem 2.12.4 (b) and the corresponding part of its proof

import Mathlib
import Definitions.Def_ProjSchedTW_Cumulative_Model

namespace ProjSchedTW.Cumulative

/-- Theorem 2.12.4, part (b) with its half of the proof: the lower inventory constraints hold
for all `t ≥ 0` iff condition (b) holds. -/
theorem lower_inventory_iff_resolves_shortage {n : ℕ} {K : Type} (P : CumulativeProject n K)
    (h2121 : TotalDemandWithinBounds P) (hRem : BoundsStraddleZero P)
    (S : Fin (n + 2) → ℝ) (hS : IsSchedule S) :
    (∀ k : K, ∀ t : ℝ, 0 ≤ t → P.Rlow k ≤ inventory P S k t) ↔ ResolvesShortageSets P S := by sorry

end ProjSchedTW.Cumulative
