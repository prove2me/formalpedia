-- Prove2me | Theorems.Thm_TIEMaximin_lemma_3_1
-- name    : TIEMaximin.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:39:57.223206+00:00
-- url     : https://prove2.me/theorems/4d055b16-03bb-4ad4-9423-1d09f2fabc9f
-- title:
--   Lemma 3.1 — closed form of the top-set competitive rule
-- statement:
--   Let $m\ge n\ge2$. For every agent $i$ and good $g$, the rule (5) satisfies
--
--   $$x_{ig}=\begin{cases}\dfrac{2n-1-f_g}{n(n-1)}\in\Bigl[\dfrac1n,\dfrac2n\Bigr],& g\in T_i,\\[2mm]\dfrac{n-1-f_g}{n(n-1)}\in\Bigl[0,\dfrac1n\Bigr],& g\notin T_i.\end{cases}$$
--
--   Moreover $\sum_{i\in N}x_{ig}=1$ for every good $g$, so $x$ is a complete fractional allocation, and $\sum_{g\in M}f_g=n(n-1)$.
--
--   These formulas are the form of the rule used in all the counting arguments.
--
--   Differences from the source:
--   - encoding: agents N, goods M, nonnegative additive valuations → `Fin n`, `Fin m` (0-based), real matrices with the hypothesis `Nonneg`, bundle value `valOf`; reason: Lean convention; same instances
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Lemma 3.1, eq. (6), p.11

import Mathlib
import Definitions.Def_TIEMaximin_Basic
import Definitions.Def_TIEMaximin_Rule

namespace TIEMaximin

/-- **Lemma 3.1** (p.11). The rule (5) is equivalent to `x_ig = (2n − 1 − f_g)/(n(n − 1)) ∈ [1/n,
2/n]` for `g ∈ T_i` and `x_ig = (n − 1 − f_g)/(n(n − 1)) ∈ [0, 1/n]` for `g ∉ T_i` (6). Moreover
`Σ_{i∈N} x_ig = 1` for every good `g`, and `Σ_{g∈M} f_g = n(n − 1)`.

arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, Lemma 3.1, eq. (6), p.11.

**Formalization Note.** `2 ≤ n ≤ m` is the paper's standing assumption (p.8). -/
theorem lemma_3_1 {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) (v : Fin n → Fin m → ℝ) (hv : Nonneg v) :
    (∀ i g, g ∈ topSet v i →
      xRule v i g = (2 * (n : ℝ) - 1 - (nom v g : ℝ)) / ((n : ℝ) * ((n : ℝ) - 1)) ∧
      1 / (n : ℝ) ≤ xRule v i g ∧ xRule v i g ≤ 2 / (n : ℝ)) ∧
    (∀ i g, g ∉ topSet v i →
      xRule v i g = ((n : ℝ) - 1 - (nom v g : ℝ)) / ((n : ℝ) * ((n : ℝ) - 1)) ∧
      0 ≤ xRule v i g ∧ xRule v i g ≤ 1 / (n : ℝ)) ∧
    (∀ g, ∑ i, xRule v i g = 1) ∧
    ∑ g, nom v g = n * (n - 1) := by sorry

end TIEMaximin
