-- Prove2me | Theorems.Thm_TarskiQuasiFPT_UpperBound_theorem_5
-- name    : TarskiQuasiFPT.UpperBound.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:40:54.021805+00:00
-- url     : https://prove2.me/theorems/aa8becf8-9ef0-4f2c-bf07-af28b3df60a3
-- title:
--   Theorem 5 — $\mathrm{SafeTarski}^*(n,k)=O(k2^k\log n\cdot\mathrm{SafeTarski}^*(n,\lfloor k/2\rfloor-1))$
-- statement:
--   For every $k\ge2$,
--   $$\mathrm{SafeTarski}^*(n,k)=O\bigl(k\,2^k\log n\cdot\mathrm{SafeTarski}^*(n,\lfloor k/2\rfloor-1)\bigr),$$
--   $\log$ being base 2. Concretely: there is one absolute constant $C$ such that for all $n\ge1$ and $k\ge2$ some deterministic algorithm outputs a solution of every safe $f:[n]^k\to[n]^k\times\{\pm1\}$ using at most
--   $$C\cdot k\,2^k\log_2 n\cdot\mathrm{SafeTarski}^*(n,\lfloor k/2\rfloor-1)$$
--   queries.
--
--   This recurrence, solved in Appendix A, gives Theorem 2.
--
--   **Formalization Note** The constant $C$ is uniform in $n$ and $k$, as Appendix A requires ('an absolute constant $D$'). The right-hand side uses the query complexity $\mathrm{SafeTarski}^*$ (with value $1$ at dimension $0$), while the left-hand side is the existence of a tree.
--
--   Differences from the source:
--   - encoding: grid [n]^k = {1,…,n}^k with the coordinatewise order → Point n k = Fin k → Fin n (values 0,…,n−1) with the pointwise order; reason: shifting every coordinate by one is an order isomorphism; no instance changes
--   - encoding: labels in {±1} with −1 < +1; positive solution (x,0) ⪯ f(x), negative solution f(x) ⪯ (x,0) → Label = {neg < pos}; IsPosSolution f x := x ⪯ (f x).1 ∧ (f x).2 = pos, IsNegSolution f x := (f x).1 ⪯ x ∧ (f x).2 = neg; reason: 0 lies strictly between −1 and +1, so 0 ≤ label iff label = +1 and label ≤ 0 iff label = −1
--   - reading: SafeTarski*(n,k) = O(·) with no stated uniformity → ∃ C : ℝ chosen before n and k (one absolute constant), and the bound stated as the existence of a decision tree that is correct on every input of the class within C·(…) queries; reason: Appendix A uses the constants as absolute ('an absolute constant D', 'a constant A' covering finitely many dimensions); a tree within the bound is the same as the query complexity being within it (the minimum is attained); this is the stronger of the possible readings
--   - reading: n is not restricted (the grid allows n = 1, where log n = 0) → n ≥ 1 included: at n = 1 the bound is 0 and the tree must make no query; reason: the source states no restriction on n; including n = 1 is the stronger reading (it holds: the grid has one point)
--   - encoding: log is base 2 (footnote 1) → Real.logb 2; reason: this is the real base-two logarithm used by the source
--   - encoding: ⌊k/2⌋ − 1 → k / 2 − 1 in ℕ; reason: ℕ-division is the floor, and k ≥ 2 makes the subtraction exact
-- source:
--   Chen, Gao, Li, Rubinstein, Yannakakis, Tarski Fixed Points in Quasi-FPT Queries, STOC 2027 submission #403 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/403.pdf, SHA-256 6a2841836f544481cc4548db5ea0222917f43c713b7a292c9947be9c149b9cd6, Theorem 5, PDF p. 5 (printed p. 4); proof §2.8, PDF p. 14 (printed p. 13), display (3)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid
import Definitions.Def_TarskiQuasiFPT_UpperBound_QueryComplexity

set_option autoImplicit false

open QAlgorithms

namespace TarskiQuasiFPT.UpperBound

/-- Theorem 5 (PDF p. 5): `SafeTarski*(n, k) = O(k 2^k log n · SafeTarski*(n, ⌊k/2⌋ − 1))` for
every `k ≥ 2`, with one absolute constant `C` (uniform in `n` and `k`): for all `n ≥ 1`, `k ≥ 2`
there is a decision tree that outputs a solution of every safe `f : [n]^k → [n]^k × {±1}` within
`C · k · 2^k · log₂ n · SafeTarski*(n, ⌊k/2⌋ − 1)` queries. -/
theorem theorem_5 :
    ∃ C : ℝ, ∀ n k : ℕ, 1 ≤ n → 2 ≤ k →
      ∃ T : DecisionTree (Point n k) (Point n k × Label) (Point n k),
        ∀ f : Point n k → Point n k × Label, IsSafe f →
          IsSolution f (T.eval f) ∧
          (T.queries f : ℝ) ≤
            C * ((k : ℝ) * 2 ^ k * Real.logb 2 n) * (safeTarskiStarQC n (k / 2 - 1) : ℝ) := by sorry

end TarskiQuasiFPT.UpperBound
