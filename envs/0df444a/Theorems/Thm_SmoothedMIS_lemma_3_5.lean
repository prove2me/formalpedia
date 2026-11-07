-- Prove2me | Theorems.Thm_SmoothedMIS_lemma_3_5
-- name    : SmoothedMIS.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:47:31.302249+00:00
-- url     : https://prove2.me/theorems/6251d96e-3a07-4f56-bd96-720278f149b3
-- title:
--   Lemma 3.5 — few sampled vertices are close
-- statement:
--   Let $F_0$ be a fixed graph with at most $n$ vertices and maximum degree at most $\Delta\ge1$, and let $V_0\subseteq V(F_0)$ be fixed. Let $1\le k\le n$, and let $\mathcal B$ contain each vertex of $V_0$ independently with probability $k/n$. A vertex $v\in\mathcal B$ is non-isolated in $F_0^2[\mathcal B]$ if some other $u\in\mathcal B$ has $\mathrm{dist}_{F_0}(u,v)\le2$. Then for every integer $q\ge2$,
--   $$
--   \mathbb P\big[\text{at least }q\text{ vertices of }\mathcal B\text{ are non-isolated in }F_0^2[\mathcal B]\big]\le\sum_{j=q}^{2q-1}(j+1)^j\Big(\frac{\Delta^4k^2}{n}\Big)^{j/2}.
--   $$
--   In particular, for every $q\ge2$, constants $C_1,C_2$ and $\varepsilon>0$ there is $n_0$ such that for $n\ge n_0$, $\Delta\ge1$ and $k\ge1$ with $\ln\Delta\le C_1\sqrt{\ln n}$ and $k\le C_2\ln n$, the right-hand side is at most $n^{-q/2+\varepsilon}$; $n_0$ does not depend on $F_0$, $V_0$, $\Delta$ or $k$.
--
--   In Case (2b) this makes the test vertices of a base-high vertex pairwise far apart, so that their outcomes are independent.
--
--   Differences from the source:
--   - reading: the right-hand side is at most n^{−q/2+o(1)} if ln ∆ = O(√ln n), k = O(ln n), q fixed, o(1) depending only on q and the implied constants → ∀ q ≥ 2, C₁, C₂, ε > 0, ∃ n0, ∀ n ≥ n0, ∀ ∆ ≥ 1, k ≥ 1 with ln ∆ ≤ C₁√ln n and k ≤ C₂ ln n: sum ≤ n^{−q/2+ε}; reason: this is the meaning of an upper bound n^{−q/2+o(1)} uniform in F0 and V0
--   - encoding: the random set B ⊆ V0 → B = {v ∈ V0 : ω v = true} with independent coins on all vertices of probability k/n; reason: same law
--   - generalization: the "in particular" clause, in the setting of the lemma (a graph F0 and 1 ≤ k ≤ n) → the bound on the sum for all real ∆ ≥ 1 and k ≥ 1 with ln ∆ ≤ C₁√ln n and k ≤ C₂ ln n, without F0 and without k ≤ n; reason: the sum depends only on n, ∆, k and q, and the paper's setting is the case k ≤ n
--   - encoding: F0 a graph with V(F0) ⊆ V and V0 ⊆ V(F0) → F0 a graph on a finite type W with card W ≤ n, V0 a set in W, ∆ and k real; reason: the statement depends only on F0 up to isomorphism, and the paper's ∆ and k are the integer cases
-- source:
--   Dey, Dufoulon, Moses Jr., Pandurangan, Smoothed Analysis for Distributed MIS (manuscript, STOC 2027 submission, sha256 dc2131db058466142db72a65b8482787f2b03f36c54eb18702fb92825cdfb42d), Lemma 3.5, p.15; Definition 3.4, p.14 (PDF pp.16–17)

import Mathlib
import Definitions.Def_SmoothedMIS_IsMIS
import Definitions.Def_SmoothedMIS_coinLaw

open MeasureTheory

namespace SmoothedMIS

/-- **Lemma 3.5 (Few sampled vertices are close)** (Dey, Dufoulon, Moses Jr., Pandurangan,
*Smoothed Analysis for Distributed MIS* (manuscript, sha256 dc2131db…), Lemma 3.5, p.15). Let `F0`
be a fixed graph with at most `n` vertices and maximum degree at most `∆ ≥ 1`, and `V0 ⊆ V(F0)`
fixed. Let `1 ≤ k ≤ n`, and let `B` contain each vertex of `V0` independently with probability
`k/n`. Then, for every integer `q ≥ 2`,
`P[at least q vertices of B are non-isolated in F0²[B]] ≤ ∑_{j=q}^{2q−1} (j+1)^j (∆⁴k²/n)^{j/2}`.
In particular, if `ln ∆ = O(√ln n)`, `k = O(ln n)` and `q` is fixed, the right-hand side is at
most `n^{−q/2+o(1)}`, the `o(1)` depending only on `q` and the implied constants.

**Formalization Note**
* `B = {v ∈ V0 : ω v}` with `ω ∼ coinLaw W (k/n)`; `v ∈ B` is non-isolated in `F0²[B]` iff some
  `u ∈ B`, `u ≠ v`, has `dist_{F0}(u, v) ≤ 2` (Definition 3.4, p.14), with `SimpleGraph.edist`.
* `∆` and `k` are real numbers; `(·)^{j/2}` is `Real.rpow`.
* The "in particular" clause: for every `q ≥ 2`, constants `C₁, C₂` and `ε > 0` there is `n0`
  such that for `n ≥ n0`, `∆ ≥ 1`, `k ≥ 1` with `ln ∆ ≤ C₁√ln n` and `k ≤ C₂ ln n`, the sum is at
  most `n^{−q/2+ε}`; `n0` does not depend on `F0`, `V0`, `∆` or `k`. -/
theorem lemma_3_5 :
    (∀ (n : ℕ) {W : Type} [Fintype W] (F0 : SimpleGraph W) (Δ : ℝ),
      Fintype.card W ≤ n → 1 ≤ Δ → (∀ v, (deg F0 v : ℝ) ≤ Δ) →
      ∀ V0 : Set W, ∀ k : ℝ, 1 ≤ k → k ≤ n → ∀ q : ℕ, 2 ≤ q →
        (coinLaw W (k / n) {ω | q ≤ {v | v ∈ V0 ∧ ω v = true ∧
            ∃ u, u ∈ V0 ∧ ω u = true ∧ u ≠ v ∧ F0.edist u v ≤ 2}.ncard}).toReal
          ≤ ∑ j ∈ Finset.Icc q (2 * q - 1),
              ((j : ℝ) + 1) ^ j * (Δ ^ 4 * k ^ 2 / n) ^ ((j : ℝ) / 2)) ∧
    ∀ q : ℕ, 2 ≤ q → ∀ C₁ C₂ ε : ℝ, 0 < ε → ∃ n0 : ℕ, ∀ n ≥ n0, ∀ Δ k : ℝ, 1 ≤ Δ → 1 ≤ k →
      Real.log Δ ≤ C₁ * Real.sqrt (Real.log n) → k ≤ C₂ * Real.log n →
        ∑ j ∈ Finset.Icc q (2 * q - 1), ((j : ℝ) + 1) ^ j * (Δ ^ 4 * k ^ 2 / n) ^ ((j : ℝ) / 2)
          ≤ (n : ℝ) ^ (-(q : ℝ) / 2 + ε) := by sorry

end SmoothedMIS
