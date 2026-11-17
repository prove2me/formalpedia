-- Prove2me | Theorems.Thm_SparseHistComm_Supplement_theorem_6
-- name    : SparseHistComm.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:46:17.066101+00:00
-- url     : https://prove2.me/theorems/ccc152b6-fcef-4a9f-b55b-fe75c8aaa26f
-- title:
--   Theorem 6 — efficient $(1+\varepsilon)$ approximation of $\Lambda$
-- statement:
--   There are universal constants $C,c>0$ such that, for every admissible $n,k,D$, rational $0<\delta<1$, and $0<\varepsilon<1$, Algorithm 1 returns a feasible homogeneous randomized covering mixture and every permitted tie-breaking output satisfies
--
--   $$
--   \Lambda_{n,k,D}(\delta)
--     \le \widehat\Lambda_{n,k,D}(\delta)
--     \le (1+\varepsilon)\Lambda_{n,k,D}(\delta).
--   $$
--
--   Its arithmetic-operation count is at most
--
--   $$
--   C\left[k+\exp\!\left(c\,
--     \frac{\log_2(8/(\varepsilon\delta))}{\varepsilon^2}
--     \log_2\!\frac{\log_2^2(8/(\varepsilon\delta))}
--     {\delta(1-\delta)\varepsilon^5}\right)\log_2(n+1)\right].
--   $$
--
--   This is the complete feasibility, approximation, and arithmetic-complexity guarantee for the actual branch-and-grid algorithm printed on page 11.
--
--   Differences from the source:
--   - encoding: Algorithm 1 returns one lower-hull minimizer but gives no tie-breaking rule → `algorithm1Returns` is a relation and the guarantee holds for every related output; reason: all ties have the same minimum cost, so every printed execution is covered
--   - encoding: the two printed big-O symbols → universal positive constants $C$ and $c$ quantified before $n,k,D,\delta,\varepsilon$; reason: this makes explicit the paper's uniform arithmetic-complexity claim and prevents hidden parameter dependence
--   - encoding: arithmetic operations of the pseudocode → the Appendix D upper-work expression `algorithm1Work`; reason: it records the candidate count, truncated polynomial exponentiation, expected-level evaluation, hull computation, and $O(k)$ binomial branch without changing the asymptotic claim
--   - encoding: probability vectors and public mixtures → points of the real standard simplex and convex combinations of at most two such points; reason: these are exactly the paper's level laws and public mixture
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Theorem 6 and Algorithm 1, p.11, (27); proof pp.22–25

import Mathlib
import Definitions.Def_SparseHistComm_Lambda
import Definitions.Def_SparseHistComm_levelSucc
import Definitions.Def_SparseHistComm_Supplement_algorithm1Returns
import Definitions.Def_SparseHistComm_Supplement_algorithm1Work

namespace SparseHistComm

namespace Supplement

/-- **Theorem 6 (Efficient approximation of the optimal policy)** (Ye–Fan, *Optimal Communication
for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256
29df82a4…f27c6f), p.11, (27), proof pp.22–25). Algorithm 1 has an output, every permitted
tie-breaking output is feasible and within factor `1+ε` of `Λ`, and its arithmetic-operation count
has the complete displayed uniform bound.

**Formalization Note** The rationality condition on `δ` is the printed Algorithm 1 input condition.
The constants `C` (outer `O`) and `c` (the `O` inside the exponent defining `f`) are quantified before
all parameters, so neither may depend on `n,k,D,ε,δ`. `algorithm1Work` is the Appendix D
arithmetic-work expression; this is arithmetic complexity, not bit complexity. -/
theorem theorem_6 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (n k : ℕ) (D δ ε : ℝ),
      1 ≤ n → 1 ≤ k → 0 ≤ D → D < k →
      0 < δ → δ < 1 → (∃ q : ℚ, (q : ℝ) = δ) → 0 < ε → ε < 1 →
      (∃ out : Algorithm1Output k, algorithm1Returns n k D δ ε out) ∧
      (∀ out : Algorithm1Output k, algorithm1Returns n k D δ ε out →
        1 - δ ≤ out.weight * levelSucc n k D out.first +
          (1 - out.weight) * levelSucc n k D out.second ∧
        Lambda n k D δ ≤ out.hatLambda ∧
        out.hatLambda ≤ (1 + ε) * Lambda n k D δ) ∧
      (algorithm1Work n k D δ ε : ℝ) ≤ C *
        ((k : ℝ) + Real.exp (c *
          (Real.logb 2 (8 / (ε * δ)) / ε ^ 2 *
            Real.logb 2 (Real.logb 2 (8 / (ε * δ)) ^ 2 /
              (δ * (1 - δ) * ε ^ 5)))) * Real.logb 2 (n + 1)) := by sorry

end Supplement

end SparseHistComm
