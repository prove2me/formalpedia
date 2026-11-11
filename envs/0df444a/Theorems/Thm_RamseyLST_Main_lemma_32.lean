-- Prove2me | Theorems.Thm_RamseyLST_Main_lemma_32
-- name    : RamseyLST.Main.lemma_32
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:08:04.263143+00:00
-- url     : https://prove2.me/theorems/168a1870-44ca-4538-b270-6a8c6cf220cf
-- title:
--   Lemma 32 — weights can be made $q$-decomposable at exponent $\vartheta = 1 - \log\log q/\log q$
-- statement:
--   Fix $q\ge16$ and put $\vartheta=1-\dfrac{\log\log q}{\log q}$ (logarithms in base 2). Let $\{x_i\}_{i\in I}$ be a finite family of nonnegative reals. Then there is a family $\{y_i\}_{i\in I}$ of nonnegative reals such that
--
--   $$y_i\le x_i^{\vartheta}\quad(i\in I),\qquad \sum_{i\in I}y_i\ge\Big(\sum_{i\in I}x_i\Big)^{\vartheta},$$
--
--   and the restriction of $\{y_i\}$ to the indices with $y_i>0$ is $q$-decomposable (Definition 11).
--
--   In the paper this lemma, from [BLMN05, Lemma 3.20], replaces the input weights by $q$-decomposable ones at the cost of the factor $\vartheta$ in the core exponent; with $q=2^t$, $\vartheta=1-\log t/t$.
--
--   Differences from the source:
--   - reading: a set {y_i}_{i∈I} (of reals) → a family y : ι → ℝ with y_i ≥ 0 for every i; reason: the y_i become the weight function w′ : Z^in → ℝ≥0 of the proof of Theorem 25 (p. 56); requiring nonnegativity is the stronger conclusion
--   - reading: a set {x_i}_{i∈I} of nonnegative reals → a family indexed by a finite type ι; reason: the sums ∑_{i∈I} are finite sums; the lemma is applied to the weights of a finite candidate core
-- source:
--   Bartal, Hovav, Nearly Tight Low-Stretch Ramsey Spanning Trees, STOC 2027 submission (manuscript sha256 bcaed0afb9db0cccb453599c9f6915e958922563d3989766c4affc99a15de44d), p. 47 (PDF 51), Lemma 32

import Mathlib
import Definitions.Def_RamseyLST_Main_Weights

namespace RamseyLST.Main

/-- Lemma 32 (p. 47, [BLMN05, Lemma 3.20]): for `q ≥ 16` and `ϑ = 1 − log log q / log q`
(base 2), every finite family of nonnegative reals `{x_i}` has a family of nonnegative reals
`{y_i}` with `y_i ≤ x_i^ϑ`, `∑ y_i ≥ (∑ x_i)^ϑ`, whose restriction to `{i : y_i > 0}` is
`q`-decomposable. -/
theorem lemma_32 (q : ℝ) (hq : 16 ≤ q) (ι : Type) [Fintype ι] [DecidableEq ι] (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧
      (∀ i, y i ≤ x i ^ (1 - Real.logb 2 (Real.logb 2 q) / Real.logb 2 q)) ∧
      (∑ i, x i) ^ (1 - Real.logb 2 (Real.logb 2 q) / Real.logb 2 q) ≤ ∑ i, y i ∧
      IsQDecomposable q (Finset.univ.filter (fun i => 0 < y i)) y := by sorry

end RamseyLST.Main
