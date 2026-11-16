-- Prove2me | Theorems.Thm_SFMQueryLower_EmptyMin_Supplement_theorem_C_9
-- name    : SFMQueryLower.EmptyMin.Supplement.theorem_C_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:31:16.272203+00:00
-- url     : https://prove2.me/theorems/0b4efdbf-101c-447e-a74d-1aea84506998
-- title:
--   Theorem C.9 — bounded-error minimization of the CGJS family needs $\Omega(n\log\log n)$ expected queries
-- statement:
--   There is an absolute constant $c>0$ such that the following holds for every even $n\ge4$. Let $A$ be a randomized value-oracle algorithm that, run on any $f\in\mathcal F$, returns a minimizer of $f$ with probability at least $2/3$. Then there is a function $f=h_{n/2}^\pi\in\mathcal F$ on which
--   $$\mathbb E\bigl[Q(A,f)\bigr]\ge c\,n\log\log n.$$
--
--   This is the lower bound of Theorem 1.5. Together with Theorem C.6 it shows that randomization lowers the query complexity of minimizing the CGJS family from $\Theta(n\log n)$ to $\Theta(n\log\log n)$.
--
--   **Formalization Note** An even $n\ge4$ is written $n=2k$ with $k\ge2$. The algorithm is a published `RandomizedOracle`; success means returning some set $T$ with $f(T)\le f(S)$ for all $S$; failure includes not returning. Correctness is assumed only on $\mathcal F$, and the expected query count may be infinite.
--
--   Differences from the source:
--   - encoding: even $n\ge4$ → $n=2k$ with $k\ge2$; reason: same set of sizes.
--   - encoding: $\Omega(n\log\log n)$ expected queries on some function → one absolute constant $c$ with the bound for every even $n\ge4$; reason: for each fixed $n$ an algorithm with success probability $2/3$ makes a positive expected number of queries on some function bounded away from $0$ (with no query its output does not depend on $\pi$, while different $\pi$ have different unique minimizers), and $n\log\log n>0$, so the eventual and the all-$n$ forms are equivalent.
-- source:
--   James Fox, Randomized Query Lower Bounds for Submodular Function Minimization, STOC 2027 submission #292 (October 2026), Theorem C.9 (lower bound of Theorem 1.5), printed p. 24 / PDF p. 25

import Definitions.Def_SFMQueryLower_EmptyMin_RandomizedOracle
import Definitions.Def_SFMQueryLower_EmptyMin_Supplement_CGJSFamily

set_option autoImplicit false
open scoped ENNReal

namespace SFMQueryLower.EmptyMin.Supplement

/-- Fox, Theorem C.9 (lower bound of Theorem 1.5), printed p. 24 / PDF p. 25.
Even `n ≥ 4` is written `n = 2k` with `k ≥ 2`. The constant `c` precedes `k` and the algorithm.
The hypothesis is only on the family `F`: on every `h_k^π` the algorithm returns some minimizer
of `h_k^π` with probability at least `2/3`. The conclusion: on some `h_k^π` the expected number
of issued value queries (in `[0, ∞]`, possibly infinite) is at least `c n log log n`. -/
theorem theorem_C_9 :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 2 ≤ k →
      ∀ A : RandomizedOracle (Finset (Fin (2 * k))) ℝ (Finset (Fin (2 * k))),
        (∀ π : Equiv.Perm (Fin (2 * k)),
          (2 / 3 : ℝ≥0∞) ≤ A.law {ω | ∃ T : Finset (Fin (2 * k)),
            Returns (A.choose ω) (cgjsFunction π) T ∧
            ∀ S : Finset (Fin (2 * k)), cgjsFunction π T ≤ cgjsFunction π S}) →
        ∃ π : Equiv.Perm (Fin (2 * k)),
          ENNReal.ofReal (c * ((2 * k : ℕ) : ℝ) * Real.log (Real.log ((2 * k : ℕ) : ℝ))) ≤
            expectedCount A (cgjsFunction π) (fun _ => True) := by sorry

end SFMQueryLower.EmptyMin.Supplement
