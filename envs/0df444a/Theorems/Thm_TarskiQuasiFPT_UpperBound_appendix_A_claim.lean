-- Prove2me | Theorems.Thm_TarskiQuasiFPT_UpperBound_appendix_A_claim
-- name    : TarskiQuasiFPT.UpperBound.appendix_A_claim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:40:50.96012+00:00
-- url     : https://prove2.me/theorems/587925c8-511f-4775-a33f-9d0f7c95e8eb
-- title:
--   Appendix A, claim in the proof of Theorem 2 — $\mathrm{SafeTarski}^*(n,r)\le A\,5^r(\log n)^{e(r)}$, $e(r)=\lceil\log((r+3)/3)\rceil$
-- statement:
--   Set $e(r)=\lceil\log_2((r+3)/3)\rceil$ for integers $r\ge0$. There is a constant $A$ such that for all $n\ge1$ and $r\ge0$
--   $$\mathrm{SafeTarski}^*(n,r)\ \le\ A\,5^r(\log_2 n)^{e(r)}.$$
--   At $r=0$ this reads $1\le A$ (as $\mathrm{SafeTarski}^*(n,0)=1$ and $e(0)=0$); for $r\ge1$ it says that some deterministic algorithm solves every safe instance of dimension $r$ with at most $A\,5^r(\log_2 n)^{e(r)}$ queries.
--
--   Combined with Lemma 1 and Theorem 4, this is the bound of Theorem 2.
--
--   **Formalization Note** $A$ is one constant, chosen before $n$ and $r$. The case $r=0$ is the convention $\mathrm{SafeTarski}^*(n,0)=1$; for $r\ge1$ the bound is stated as the existence of a tree.
--
--   Differences from the source:
--   - encoding: grid [n]^k = {1,…,n}^k with the coordinatewise order → Point n k = Fin k → Fin n (values 0,…,n−1) with the pointwise order; reason: shifting every coordinate by one is an order isomorphism; no instance changes
--   - encoding: labels in {±1} with −1 < +1; positive solution (x,0) ⪯ f(x), negative solution f(x) ⪯ (x,0) → Label = {neg < pos}; IsPosSolution f x := x ⪯ (f x).1 ∧ (f x).2 = pos, IsNegSolution f x := (f x).1 ⪯ x ∧ (f x).2 = neg; reason: 0 lies strictly between −1 and +1, so 0 ≤ label iff label = +1 and label ≤ 0 iff label = −1
--   - reading: the constant A with no stated uniformity → ∃ A : ℝ chosen before n and r (one absolute constant), with 1 ≤ A and a correct decision tree within A·5^r·(log₂ n)^e(r) queries for r ≥ 1; reason: Appendix A uses the constants as absolute ('an absolute constant D', 'a constant A' covering finitely many dimensions); a tree within the bound is the same as the query complexity being within it (the minimum is attained); this is the stronger of the possible readings
--   - reading: n is not restricted (the grid allows n = 1, where log n = 0) → n ≥ 1 included: at n = 1 and r ≥ 1 the bound is 0 and the tree must make no query; at r = 0 the bound is 1 ≤ A; reason: the source states no restriction on n; the single grid point solves every positive-dimensional instance without queries, while dimension zero retains the explicit complexity convention
--   - encoding: log is base 2 (footnote 1) and ⌈·⌉ is the integer ceiling → Real.logb 2 and Int.ceil, converted to ℕ by Int.toNat, used as a natural-number exponent; reason: the ceiling's argument is ≥ 0 in every instance, so toNat is exact; a natural exponent gives (log₂ 1)^0 = 1
-- source:
--   Chen, Gao, Li, Rubinstein, Yannakakis, Tarski Fixed Points in Quasi-FPT Queries, STOC 2027 submission #403 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/403.pdf, SHA-256 6a2841836f544481cc4548db5ea0222917f43c713b7a292c9947be9c149b9cd6, Appendix A, claim in the proof of Theorem 2, PDF p. 28 (printed p. 27)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid
import Definitions.Def_TarskiQuasiFPT_UpperBound_QueryComplexity

set_option autoImplicit false

open QAlgorithms

namespace TarskiQuasiFPT.UpperBound

/-- The claim in the proof of Theorem 2 (Appendix A, PDF p. 28): with
`e(r) = ⌈log₂((r + 3)/3)⌉`, there is a constant `A` with `SafeTarski*(n, r) ≤ A 5^r (log n)^{e(r)}`
for all `n ≥ 1`, `r ≥ 0`. At `r = 0` (where `SafeTarski*(n, 0) = 1` by convention and `e(0) = 0`)
this is `1 ≤ A`; for `r ≥ 1` it is the existence of a decision tree solving every safe instance
within `A · 5^r · (log₂ n)^{e(r)}` queries. -/
theorem appendix_A_claim :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ n r : ℕ, 1 ≤ n → 1 ≤ r →
      ∃ T : DecisionTree (Point n r) (Point n r × Label) (Point n r),
        ∀ f : Point n r → Point n r × Label, IsSafe f →
          IsSolution f (T.eval f) ∧
          (T.queries f : ℝ) ≤
            A * 5 ^ r * Real.logb 2 n ^ (⌈Real.logb 2 (((r : ℝ) + 3) / 3)⌉).toNat := by sorry

end TarskiQuasiFPT.UpperBound
