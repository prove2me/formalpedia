-- Prove2me | Theorems.Thm_Supermodularity_Matching_exists_increasing_optimal_matching_and_tight_optimality
-- name    : Supermodularity.Matching.exists_increasing_optimal_matching_and_tight_optimality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T21:24:38.793974+00:00
-- url     : https://prove2.me/theorems/e7282143-ae20-452b-a374-c35e9dc9227b
-- title:
--   Theorem 3.2.3 — existence of an increasing optimal matching, and tight-market optimality
-- statement:
--   Suppose $f(x,j)$ is supermodular in the joint variable $(x,j)$ on $\bigl(\prod_{i=1}^n
--   X_i\bigr) \times \{1,\dots,m\}$ — with no hypothesis that the labor market is loose. Then:
--
--   1. there exists an increasing optimal matching (`IsIncreasingMatching` and
--      `IsOptimalMatching`); and
--   2. if, in addition, the labor market is tight (every worker type has exactly $m$ available
--      workers, `Fintype.card (X i) = m` for every $i$), then every tight, increasing matching
--      $x$ is at least as profitable as every other tight matching $y$:
--      $$\sum_{j=1}^m f(y^j,j) \;\le\; \sum_{j=1}^m f(x^j,j).$$
--
--   Topkis, Theorem 3.2.3 (p. 99–100): "If $f(x,j)$ is supermodular in $(x,j)$ on
--   $\times_{i=1}^n X_i \times \{1,\dots,m\}$, then there exists an increasing optimal matching
--   of workers to firms. If, in addition, the labor market is tight, then each increasing
--   matching is optimal." The proof (unlike Theorem 3.2.1's, which reduces to per-firm
--   optimization) is a direct, non-constructive argument: it picks an optimal matching that
--   lexicographically minimizes the failure of the increasing property, and shows that if it is
--   not already increasing, swapping two firms' assignments via $\vee,\wedge$ produces a
--   strictly more profitable matching — contradicting optimality, by the supermodularity of $f$.
--
--   **Formalization Note.** Part (2) is stated as a direct profit comparison — "every tight
--   increasing matching beats every tight matching" — rather than by reusing the general,
--   unconstrained `IsOptimalMatching f x` predicate for `x`, since in a tight labor market the
--   feasible matchings are exactly the tight ones (`IsTightMatching`), and the book's "each
--   increasing matching is optimal" is a claim about optimality *among* those feasible tight
--   matchings, not among every function $\mathrm{Fin}\,m \to \prod_i X_i$ unconstrained. This is
--   the mission's goal theorem: it needs no loose-labor-market hypothesis, and its harder,
--   non-constructive proof is why Theorem 3.2.1 (which does assume a loose market) is kept as a
--   separate, easier milestone rather than being subsumed.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 99-100, Theorem 3.2.3

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_Supermodularity_Matching_IsOptimalMatching
import Definitions.Def_Supermodularity_Matching_IsIncreasingMatching
import Definitions.Def_Supermodularity_Matching_IsTightMatching

namespace Supermodularity.Matching

theorem exists_increasing_optimal_matching_and_tight_optimality
    {n m : ℕ} {X : Fin n → Type*} [∀ i, Lattice (X i)] [∀ i, Fintype (X i)]
    [∀ i, Nonempty (X i)]
    (f : (∀ i, X i) → Fin m → ℝ)
    (hf : Supermodularity.Monotonicity.SupermodularOn
      (fun p : (∀ i, X i) × Fin m => f p.1 p.2) Set.univ) :
    (∃ x : Fin m → ∀ i, X i, IsIncreasingMatching x ∧ IsOptimalMatching f x) ∧
      ((∀ i, Fintype.card (X i) = m) →
        ∀ x : Fin m → ∀ i, X i, IsTightMatching x → IsIncreasingMatching x →
          ∀ y : Fin m → ∀ i, X i, IsTightMatching y → ∑ j, f (y j) j ≤ ∑ j, f (x j) j) := by sorry

end Supermodularity.Matching
