-- Prove2me | Theorems.Thm_TarskiQuasiFPT_UpperBound_lemma_1
-- name    : TarskiQuasiFPT.UpperBound.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:41:02.03409+00:00
-- url     : https://prove2.me/theorems/d54e6d67-813d-4bef-bdeb-0e2e49d401b1
-- title:
--   Lemma 1 (Folklore) — $\mathrm{Tarski}(n,k)=O((\log n)\cdot\mathrm{Tarski}^*(n,k-1))$
-- statement:
--   For every $k\ge1$,
--   $$\mathrm{Tarski}(n,k)=O\bigl((\log n)\cdot\mathrm{Tarski}^*(n,k-1)\bigr).$$
--   Concretely: there is one absolute constant $C$ such that for all $n\ge1$ and $k\ge1$ some deterministic algorithm outputs a fixed point of every monotone $f:[n]^k\to[n]^k$ with at most $C\log_2 n\cdot\mathrm{Tarski}^*(n,k-1)$ queries (with $\mathrm{Tarski}^*(n,0)=1$).
--
--   This binary-search reduction is cited in the paper ([FPS22, CL22]; sketch in [CLY26]) and used in Appendix A as display (9).
--
--   **Formalization Note** The constant is uniform in $k$, which Appendix A needs to keep the factor $5^k$.
--
--   Differences from the source:
--   - encoding: grid [n]^k = {1,…,n}^k with the coordinatewise order → Point n k = Fin k → Fin n (values 0,…,n−1) with the pointwise order; reason: shifting every coordinate by one is an order isomorphism; no instance changes
--   - encoding: labels in {±1} with −1 < +1; positive solution (x,0) ⪯ f(x), negative solution f(x) ⪯ (x,0) → Label = {neg < pos}; IsPosSolution f x := x ⪯ (f x).1 ∧ (f x).2 = pos, IsNegSolution f x := (f x).1 ⪯ x ∧ (f x).2 = neg; reason: 0 lies strictly between −1 and +1, so 0 ≤ label iff label = +1 and label ≤ 0 iff label = −1
--   - reading: Tarski(n,k) = O(·) with no stated uniformity → ∃ C : ℝ chosen before n and k (one absolute constant), and the bound stated as the existence of a decision tree that is correct on every input of the class within C·(…) queries; reason: Appendix A uses the constants as absolute ('an absolute constant D', 'a constant A' covering finitely many dimensions); a tree within the bound is the same as the query complexity being within it (the minimum is attained); this is the stronger of the possible readings
--   - reading: n is not restricted (the grid allows n = 1, where log n = 0) → n ≥ 1 included: at n = 1 the bound is 0 and the tree must make no query; reason: the source states no restriction on n; including n = 1 is the stronger reading (it holds: the grid has one point)
--   - encoding: log is base 2 (footnote 1) → Real.logb 2; reason: this is the real base-two logarithm used by the source
-- source:
--   Chen, Gao, Li, Rubinstein, Yannakakis, Tarski Fixed Points in Quasi-FPT Queries, STOC 2027 submission #403 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/403.pdf, SHA-256 6a2841836f544481cc4548db5ea0222917f43c713b7a292c9947be9c149b9cd6, Lemma 1, PDF p. 4 (printed p. 3); cited from [FPS22, CL22]

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid
import Definitions.Def_TarskiQuasiFPT_UpperBound_QueryComplexity

set_option autoImplicit false

open QAlgorithms

namespace TarskiQuasiFPT.UpperBound

/-- Lemma 1 (Folklore; PDF p. 4): `Tarski(n, k) = O((log n) · Tarski*(n, k − 1))` for every
`k ≥ 1`, with one absolute constant `C` (uniform in `n` and `k`): for all `n ≥ 1`, `k ≥ 1` there
is a decision tree that outputs a fixed point of every monotone `f : [n]^k → [n]^k` within
`C · log₂ n · Tarski*(n, k − 1)` queries. -/
theorem lemma_1 :
    ∃ C : ℝ, ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      ∃ T : DecisionTree (Point n k) (Point n k) (Point n k),
        ∀ f : Point n k → Point n k, Monotone f →
          f (T.eval f) = T.eval f ∧
          (T.queries f : ℝ) ≤ C * Real.logb 2 n * (tarskiStarQC n (k - 1) : ℝ) := by sorry

end TarskiQuasiFPT.UpperBound
