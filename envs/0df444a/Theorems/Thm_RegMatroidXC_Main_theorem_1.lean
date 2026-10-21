-- Prove2me | Theorems.Thm_RegMatroidXC_Main_theorem_1
-- name    : RegMatroidXC.Main.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:42.450871+00:00
-- url     : https://prove2.me/theorems/e7d0b113-49c3-48cd-8210-4c595715406e
-- title:
--   Theorem 1 (main theorem) — xc(P(M)) ≤ c₀ · n⁶ for every regular matroid M on n elements
-- statement:
--   For a matroid $M$ with ground set $E(M)$, the independence polytope is $P(M) = \operatorname{conv}\{\chi^I \in \{0,1\}^{E(M)} \mid I \text{ independent in } M\}$. A matroid is regular if it can be represented over the reals by a totally unimodular matrix. The extension complexity $\mathrm{xc}(P)$ of a polytope $P$ is the minimum number of inequalities in an extended formulation of $P$, i.e. a linear system in $(x, y)$ such that $x \in P$ exactly when some $y$ satisfies it.
--
--   **Theorem.** There is a constant $c_0$ such that for every regular matroid $M$ on $n$ elements
--   $$\mathrm{xc}(P(M)) \le c_0 \cdot n^6 .$$
--
--   This is the first polynomial upper bound on the extension complexity of the independence polytope of a regular matroid: optimizing a linear function over the independent sets of a regular matroid can be written as a linear program of size polynomial in $n$.
--
--   **Formalization Note** The bound is stated as the existence, for every regular $M$, of an extended formulation of $P(M) \subseteq \mathbb R^{E(M)}$ with at most $c_0 n^6$ inequalities, where $n = |E(M)|$ and $c_0$ is chosen before the ambient type and the matroid. Loops are allowed.
-- source:
--   Aprile & Fiorini, Regular Matroids Have Polynomial Extension Complexity, arXiv:1909.08539v2, p. 2, Theorem 1 (proof p. 4)

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_RegMatroidXC_Main_Matroids
open ExtensionComplexity.TSP

namespace RegMatroidXC.Main

theorem theorem_1 : ∃ c₀ : ℝ, ∀ (α : Type) (M : Matroid α) [Fintype M.E], IsRegular M →
    ∃ r : ℕ, IsEFOfSize (indepPolytope M) r ∧ (r : ℝ) ≤ c₀ * (Fintype.card M.E : ℝ) ^ 6 := by sorry

end RegMatroidXC.Main
