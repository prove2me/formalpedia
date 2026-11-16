-- Prove2me | Theorems.Thm_SFMQueryLower_EmptyMin_Supplement_theorem_C_6
-- name    : SFMQueryLower.EmptyMin.Supplement.theorem_C_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:29:30.114168+00:00
-- url     : https://prove2.me/theorems/37198507-cd4c-4a64-98cd-589862f0e002
-- title:
--   Theorem C.6 — a zero-error randomized algorithm minimizes the CGJS family with $O(n\log\log n)$ expected queries
-- statement:
--   There is an absolute constant $C>0$ such that for every even $n\ge4$ there is a randomized value-oracle algorithm $A$ with the following property: for every permutation $\pi$ of $[n]$, run on $h_{n/2}^\pi\in\mathcal F$, the algorithm returns the unique minimizer $P^\pi$ with probability $1$, and its expected number of value queries satisfies
--   $$\mathbb E\bigl[Q(A,h_{n/2}^\pi)\bigr]\le C\,n\log\log n.$$
--
--   This is the upper bound of Theorem 1.5; with Theorem C.9 it gives $\Theta(n\log\log n)$ for the randomized query complexity of minimizing the CGJS family, below the deterministic $\Theta(n\log n)$.
--
--   **Formalization Note** An even $n\ge4$ is written $n=2k$ with $k\ge2$. Randomized algorithms are the published `RandomizedOracle` (arbitrary seed space); expectations are in $[0,\infty]$ and count every issued query. Correctness is required only on $\mathcal F$. $\log$ is the natural logarithm, and $\log\log n>0$ for $n\ge4$.
--
--   Differences from the source:
--   - encoding: even $n\ge4$ → $n=2k$ with $k\ge2$; reason: same set of sizes.
--   - encoding: $O(n\log\log n)$ expected queries → one absolute constant $C$ with expected count at most $C n\log\log n$ for every even $n\ge4$; reason: for each fixed $n$ exhaustive querying is a zero-error algorithm with finite cost and $n\log\log n>0$, so the eventual and the all-$n$ forms are equivalent.
--   - encoding: "returns its unique minimizer" → returns $P^\pi$ with probability $1$; reason: $P^\pi$ is the unique minimizer (Lemma C.2), and the source's proof identifies the returned set as $P^\pi$.
-- source:
--   James Fox, Randomized Query Lower Bounds for Submodular Function Minimization, STOC 2027 submission #292 (October 2026), Theorem C.6 (upper bound of Theorem 1.5), printed p. 22 / PDF p. 23

import Definitions.Def_SFMQueryLower_EmptyMin_RandomizedOracle
import Definitions.Def_SFMQueryLower_EmptyMin_Supplement_CGJSFamily

set_option autoImplicit false
open scoped ENNReal

namespace SFMQueryLower.EmptyMin.Supplement

/-- Fox, Theorem C.6 (upper bound of Theorem 1.5), printed p. 22 / PDF p. 23.
Even `n ≥ 4` is written `n = 2k` with `k ≥ 2`. The constant `C` precedes `k` and the algorithm.
Zero error: on every `h ∈ F` the algorithm returns `P^π` (the unique minimizer, Lemma C.2) with
probability exactly `1`. The cost is the expected number of issued value queries in `[0, ∞]`. -/
theorem theorem_C_6 :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 2 ≤ k →
      ∃ A : RandomizedOracle (Finset (Fin (2 * k))) ℝ (Finset (Fin (2 * k))),
        ∀ π : Equiv.Perm (Fin (2 * k)),
          A.law {ω | Returns (A.choose ω) (cgjsFunction π) (cgjsMinimizer π)} = 1 ∧
          expectedCount A (cgjsFunction π) (fun _ => True) ≤
            ENNReal.ofReal (C * ((2 * k : ℕ) : ℝ) * Real.log (Real.log ((2 * k : ℕ) : ℝ))) := by sorry

end SFMQueryLower.EmptyMin.Supplement
