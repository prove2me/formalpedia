-- Prove2me | Theorems.Thm_RegMatroidXC_Main_wong_martin_bound
-- name    : RegMatroidXC.Main.wong_martin_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:21.295992+00:00
-- url     : https://prove2.me/theorems/86676652-bf06-41b7-b3f3-73d35bdf6635
-- title:
--   Wong–Martin bound (p. 1) — xc(P(M)) = O(n²) for graphic and cographic matroids
-- statement:
--   For a polytope $P$, an *extended formulation* of size $r$ is a linear system in variables $(x, y)$ with $r$ inequalities (and any number of equations) such that $x \in P$ if and only if some $y$ satisfies the system; the extension complexity $\mathrm{xc}(P)$ is the least such $r$.
--
--   There is an absolute constant $c$ such that for every matroid $M$ on $n$ elements that is graphic or cographic, the independence polytope $P(M)$ has an extended formulation with at most $c \cdot n^2$ inequalities:
--   $$\mathrm{xc}(P(M)) \le c\, n^2 .$$
--
--   This is the base case of the induction proving the main theorem; it goes back to the extended formulations of the spanning tree polytope due to Wong and Martin.
--
--   **Formalization Note** The bound is stated as the existence of an extended formulation of size at most $c n^2$, with $c$ chosen before the matroid. $P(M)$ lives in $\mathbb R^{E(M)}$.
-- source:
--   Aprile & Fiorini, Regular Matroids Have Polynomial Extension Complexity, arXiv:1909.08539v2, p. 1, Section 1 (Wong [25], Martin [14])

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_RegMatroidXC_Main_Matroids
open ExtensionComplexity.TSP

namespace RegMatroidXC.Main

theorem wong_martin_bound : ∃ c : ℝ, ∀ (α : Type) (M : Matroid α) [Fintype M.E],
    (IsGraphic M ∨ IsCographic M) →
    ∃ r : ℕ, IsEFOfSize (indepPolytope M) r ∧ (r : ℝ) ≤ c * (Fintype.card M.E : ℝ) ^ 2 := by sorry

end RegMatroidXC.Main
