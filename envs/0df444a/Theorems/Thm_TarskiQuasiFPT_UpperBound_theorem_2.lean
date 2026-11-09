-- Prove2me | Theorems.Thm_TarskiQuasiFPT_UpperBound_theorem_2
-- name    : TarskiQuasiFPT.UpperBound.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:40:53.750628+00:00
-- url     : https://prove2.me/theorems/2a0fef92-c530-48da-8281-170b13fd0f0a
-- title:
--   Theorem 2 — a deterministic $O(5^k(\log n)^{1+\lceil\log((k+2)/3)\rceil})=O(5^k(\log n)^{\lceil\log k\rceil})$-query algorithm for Tarski$(n,k)$, $k\ge3$
-- statement:
--   For $k\ge3$ there is a deterministic algorithm for $\mathrm{Tarski}(n,k)$ with query complexity
--   $$O\Bigl(5^k(\log n)^{1+\lceil\log((k+2)/3)\rceil}\Bigr)=O\Bigl(5^k(\log n)^{\lceil\log k\rceil}\Bigr),$$
--   $\log$ being base 2. Concretely: there is one absolute constant $C$ such that for all $n\ge1$ and $k\ge3$ some deterministic algorithm, querying points $x\in[n]^k$ and receiving the whole vector $f(x)$, outputs a fixed point of every monotone $f:[n]^k\to[n]^k$ and makes at most
--   $$C\,5^k(\log_2 n)^{1+\lceil\log_2((k+2)/3)\rceil}\qquad\text{and at most}\qquad C\,5^k(\log_2 n)^{\lceil\log_2 k\rceil}$$
--   queries.
--
--   This is the paper's main upper bound: the exponent of $\log n$ grows only logarithmically in the dimension, against the $\log^{O(k)} n$ bounds known before.
--
--   **Formalization Note** Both bounds of the display are kept as separate conclusions. The factor is exactly $5^k$ and the exponents are exactly those printed; the constant $C$ does not depend on $n$ or $k$. Correctness is required for every monotone $f$, not only for functions with a unique fixed point.
--
--   Differences from the source:
--   - encoding: grid [n]^k = {1,…,n}^k with the coordinatewise order → Point n k = Fin k → Fin n (values 0,…,n−1) with the pointwise order; reason: shifting every coordinate by one is an order isomorphism; no instance changes
--   - reading: the query complexity = O(·) with no stated uniformity → ∃ C : ℝ chosen before n and k (one absolute constant), and the bound stated as the existence of a decision tree that is correct on every input of the class within C·(…) queries; reason: Appendix A uses the constants as absolute ('an absolute constant D', 'a constant A' covering finitely many dimensions); a tree within the bound is the same as the query complexity being within it (the minimum is attained); this is the stronger of the possible readings
--   - reading: n is not restricted (the grid allows n = 1, where log n = 0) → n ≥ 1 included: at n = 1 the bound is 0 and the tree must make no query; reason: the source states no restriction on n; including n = 1 is the stronger reading (it holds: the grid has one point)
--   - encoding: log is base 2 (footnote 1) and ⌈·⌉ is the integer ceiling → Real.logb 2 and Int.ceil, converted to ℕ by Int.toNat, used as a natural-number exponent; reason: the ceiling's argument is ≥ 0 in every instance, so toNat is exact; a natural exponent gives (log₂ 1)^0 = 1
-- source:
--   Chen, Gao, Li, Rubinstein, Yannakakis, Tarski Fixed Points in Quasi-FPT Queries, STOC 2027 submission #403 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/403.pdf, SHA-256 6a2841836f544481cc4548db5ea0222917f43c713b7a292c9947be9c149b9cd6, Theorem 2, PDF p. 3 (printed p. 2); proof Appendix A, PDF pp. 28–29 (printed pp. 27–28)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid
import Definitions.Def_TarskiQuasiFPT_UpperBound_QueryComplexity

set_option autoImplicit false

open QAlgorithms

namespace TarskiQuasiFPT.UpperBound

/-- Theorem 2 (PDF p. 3): for `k ≥ 3` there is a deterministic algorithm for `Tarski(n, k)` with
query complexity `O(5^k (log n)^{1+⌈log((k+2)/3)⌉}) = O(5^k (log n)^{⌈log k⌉})` (log base 2), with
one absolute constant `C` (uniform in `n` and `k`): for all `n ≥ 1`, `k ≥ 3` there is a decision
tree that outputs a fixed point of every monotone `f : [n]^k → [n]^k`, making at most
`C · 5^k · (log₂ n)^{1+⌈log₂((k+2)/3)⌉}` and at most `C · 5^k · (log₂ n)^{⌈log₂ k⌉}` queries. -/
theorem theorem_2 :
    ∃ C : ℝ, ∀ n k : ℕ, 1 ≤ n → 3 ≤ k →
      ∃ T : DecisionTree (Point n k) (Point n k) (Point n k),
        ∀ f : Point n k → Point n k, Monotone f →
          f (T.eval f) = T.eval f ∧
          (T.queries f : ℝ) ≤
            C * 5 ^ k * Real.logb 2 n ^ (1 + (⌈Real.logb 2 (((k : ℝ) + 2) / 3)⌉).toNat) ∧
          (T.queries f : ℝ) ≤ C * 5 ^ k * Real.logb 2 n ^ (⌈Real.logb 2 (k : ℝ)⌉).toNat := by sorry

end TarskiQuasiFPT.UpperBound
