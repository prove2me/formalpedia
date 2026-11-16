-- Prove2me | Theorems.Thm_TarskiQuasiFPT_UpperBound_Supplement_theorem_3
-- name    : TarskiQuasiFPT.UpperBound.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:32:54.255313+00:00
-- url     : https://prove2.me/theorems/3c4df4fe-a8e7-4bf7-976c-ff29143ab1f5
-- title:
--   Theorem 3 — randomized lower bound $\Omega((\log n/\mathrm{polylog}(k))^{\lfloor\log_4(6k+4)\rfloor})$ for $\mathrm{Tarski}(n,k)$
-- statement:
--   Let $k\ge2$. A randomized algorithm for $\mathrm{Tarski}(n,k)$ queries points $x\in[n]^k$ of a monotone $f:[n]^k\to[n]^k$, each query returning the whole vector $f(x)$. It must output a fixed point with probability $1$; equivalently, it is a probability distribution over deterministic decision trees, each of which always outputs a fixed point. Its cost on $f$ is the expected number of queries.
--
--   Theorem 3 states that every such algorithm needs
--   $$\Omega\!\left(\Big(\frac{\log n}{\mathrm{polylog}(k)}\Big)^{\lfloor\log_4(6k+4)\rfloor}\right)$$
--   queries in expectation in the worst case, even when the input has a unique fixed point.
--
--   Concretely, there are absolute constants $c>0$, $C>0$ and $d\in\mathbb N$ with the following property. For all $k\ge2$ and $n\ge1$, and every distribution $R$ over deterministic trees each of which outputs a fixed point of every monotone $f$ that has a unique fixed point, there is a monotone $f$ with a unique fixed point such that
--   $$\mathbb E_{T\sim R}\big[\#\text{queries of }T\text{ on }f\big]\ \ge\ c\Big(\frac{\log n}{C(\log k)^d}\Big)^{\lfloor\log_4(6k+4)\rfloor}.$$
--
--   This is the paper's lower bound. It is a companion to the mission's goal (Theorem 2, the quasi-FPT upper bound): both exponents grow logarithmically in $k$. The paper derives it from Theorem 6.
--
--   **Formalization Note** $\Omega$ and $\mathrm{polylog}(k)$ are read uniformly: $c$, $C$ and $d$ are fixed before $k$ and $n$, and no threshold on $n$ is added. $\log$ is base two, and $\lfloor\log_4(6k+4)\rfloor$ is `Nat.log 4 (6k+4)`. The expected cost is an extended-nonnegative-real sum over the trees in $R$, and is infinite when unbounded.
--
--   Differences from the source:
--   - encoding: [n] = {1,…,n}, points of [n]^k ordered coordinatewise → Point n k = Fin k → Fin n (0-based values) with the pointwise order; reason: shift by one; same order, same instances
--   - encoding: log (base two, footnote 1) → Real.logb 2; reason: the paper's convention
--   - reading: Ω(·) and polylog(k) (asymptotic notation) → ∃ c > 0, ∃ C > 0, ∃ d : ℕ, fixed before k and n, bound c·(log n/(C·(log k)^d))^{⌊log₄(6k+4)⌋} for every k ≥ 2 and n ≥ 1; reason: the strongest standard reading of the asymptotic statement: constants absolute and no "n sufficiently large" threshold (below the paper's threshold the right side is < 1 for large C, while every correct tree makes ≥ 1 query when n ≥ 2, and the right side is 0 at n = 1)
--   - reading: "any randomized algorithm for Tarski(n, k) (with probability 1) … even when the input function has a unique fixed point" → R : RandDecisionTree with every tree in its support outputting a fixed point of every monotone f that has a unique fixed point; the hard f is monotone with a unique fixed point; reason: correctness with probability 1 means every tree in the support is correct; requiring correctness only under the unique-fixed-point promise admits more algorithms, so it is the stronger lower bound
--   - encoding: queries in expectation → ∑' T, R T * T.queries f in ℝ≥0∞ against ENNReal.ofReal of the bound; reason: expected value of a nonnegative integer variable; may be infinite
--   - encoding: n a side length → 1 ≤ n; reason: [0]^k is empty for k ≥ 2; excludes only the empty grid
-- source:
--   Chen, Gao, Li, Rubinstein, Yannakakis, Tarski Fixed Points in Quasi-FPT Queries, STOC 2027 submission #403 (October 2026), SHA-256 6a2841836f544481cc4548db5ea0222917f43c713b7a292c9947be9c149b9cd6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/403.pdf, Theorem 3, PDF p. 3 (printed p. 2); restated PDF p. 14 (printed p. 13); derivation from Theorem 6, PDF p. 15 (printed p. 14)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid
import Definitions.Def_TarskiQuasiFPT_UpperBound_Supplement_LowerBound

open QAlgorithms
set_option autoImplicit false

open scoped ENNReal

namespace TarskiQuasiFPT.UpperBound.Supplement

/-- Theorem 3, PDF p. 3 (restated p. 14). For `k ≥ 2`, every randomized (Las Vegas) algorithm
for `Tarski(n, k)`, i.e. a distribution `R` over deterministic decision trees each of which outputs
a fixed point of every monotone input with a unique fixed point, makes
`Ω((log n / polylog(k))^{⌊log₄(6k+4)⌋})` queries in expectation on some monotone input with a
unique fixed point. The constants `c, C > 0` and the polylog degree `d` are absolute. -/
theorem theorem_3 :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ k : ℕ, 2 ≤ k → ∀ n : ℕ, 1 ≤ n →
      ∀ R : RandDecisionTree (Point n k) (Point n k) (Point n k),
        (∀ T ∈ R.support, ∀ f : Point n k → Point n k, Monotone f → HasUniqueFixedPoint f →
          f (T.eval f) = T.eval f) →
        ∃ f : Point n k → Point n k, Monotone f ∧ HasUniqueFixedPoint f ∧
          ENNReal.ofReal
              (c * (Real.logb 2 n / (C * Real.logb 2 k ^ d)) ^ Nat.log 4 (6 * k + 4))
            ≤ ∑' T, R T * (T.queries f : ℝ≥0∞) := by sorry

end TarskiQuasiFPT.UpperBound.Supplement
