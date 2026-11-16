-- Prove2me | Theorems.Thm_TarskiQuasiFPT_UpperBound_Supplement_lemma_13
-- name    : TarskiQuasiFPT.UpperBound.Supplement.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:29:28.936701+00:00
-- url     : https://prove2.me/theorems/7019045c-66e5-4ede-9921-3524437e5dff
-- title:
--   Lemma 13 ([EPRY20]) — a herringbone distribution on $[m]^2$: depth $c_0(\log m)^2$ succeeds w.p. at most $m^{-c_0-1/8}$
-- statement:
--   This is the two-dimensional base case of the lower bound, from the herringbone construction of Etessami, Papadimitriou, Rubinstein and Yannakakis [EPRY20]. A query at $x$ returns the whole vector $F(x)$, and a decision tree finds the fixed point if its output is the fixed point of $F$.
--
--   There is a universal constant $c_0>0$ with the following property. For every integer $m\ge200$ there is a distribution $\mathcal F$ of monotone functions $F:[m]^2\to[m]^2$ such that:
--
--   1. every $F\in\operatorname{supp}(\mathcal F)$ has a unique fixed point;
--   2. for $F\sim\mathcal F$, every deterministic decision tree of depth at most $q=c_0(\log m)^2$ satisfies
--   $$\Pr_{F\sim\mathcal F}\big[\text{the tree finds the fixed point of }F\big]\le m^{-c_0-1/8}.$$
--
--   Here $\log$ is base two. The lemma is level $\ell=1$ of the paper's induction for Theorem 6. Footnote 5 of the paper notes that [EPRY20] states only an $\Omega((\log m)^2)$ randomized bound, and that this probability form follows from their construction and analysis.
--
--   **Formalization Note** $c_0$ is chosen before $m$ and is uniform over all $m\ge200$. The probability is the outer measure of the PMF on the set of $F$ for which the tree's output is a fixed point of $F$.
--
--   Differences from the source:
--   - encoding: [n] = {1,…,n}, points of [n]^k ordered coordinatewise → Point n k = Fin k → Fin n (0-based values) with the pointwise order; reason: shift by one; same order, same instances
--   - encoding: a distribution of functions → PMF over functions; reason: the function spaces are finite, so every distribution is a PMF
--   - encoding: deterministic decision tree of depth at most q → DepthLE T q: T.queries g ≤ q for every oracle g (q real); reason: depth is the longest root-to-leaf path; the real bound is the paper's real expression
--   - reading: the tree "finds the fixed point" of F → the output T.eval F is a fixed point of F; reason: §3 uses "finds" for the output; for a lower bound this is the stronger of the two readings (a tree that queried the fixed point can output it at no extra depth)
--   - encoding: log (base two, footnote 1) → Real.logb 2; reason: the paper's convention
-- source:
--   Chen, Gao, Li, Rubinstein, Yannakakis, Tarski Fixed Points in Quasi-FPT Queries, STOC 2027 submission #403 (October 2026), SHA-256 6a2841836f544481cc4548db5ea0222917f43c713b7a292c9947be9c149b9cd6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/403.pdf, Lemma 13, PDF p. 16 (printed p. 15), with footnote 5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid
import Definitions.Def_TarskiQuasiFPT_UpperBound_Supplement_LowerBound

open QAlgorithms
set_option autoImplicit false

namespace TarskiQuasiFPT.UpperBound.Supplement

/-- Lemma 13 ([EPRY20]), PDF p. 16: there is a universal `c0 > 0` such that for every integer
`m ≥ 200` there is a distribution of monotone `F : [m]^2 → [m]^2`, each with a unique fixed point,
such that every deterministic decision tree of depth at most `q = c0 (log₂ m)^2` finds the fixed
point of `F ∼ 𝓕` with probability at most `m^{−c0−1/8}`. -/
theorem lemma_13 :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ m : ℕ, 200 ≤ m →
      ∃ D : PMF (Point m 2 → Point m 2),
        (∀ F ∈ D.support, Monotone F ∧ HasUniqueFixedPoint F) ∧
        ∀ T : DecisionTree (Point m 2) (Point m 2) (Point m 2),
          DepthLE T (c0 * Real.logb 2 m ^ 2) →
            succProb D T ≤ (m : ℝ) ^ (-c0 - 1 / 8) := by sorry

end TarskiQuasiFPT.UpperBound.Supplement
