-- Prove2me | Theorems.Thm_TightQLearning_theorem_6
-- name    : TightQLearning.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:30:27.407545+00:00
-- url     : https://prove2.me/theorems/cde7adde-8af0-42c7-8d55-1580fbc93aa8
-- title:
--   Theorem 6 — Freedman's inequality (56) and its peeled form (57)
-- statement:
--   Let $(\mathcal F_k)$ be a filtration, and let $X_1,\dots,X_n$ be real random variables with $X_k$ being $\mathcal F_k$-measurable, $\mathbb E[X_k\mid\mathcal F_{k-1}]=0$ and $|X_k|\le R$. Write $Y_n=\sum_{k=1}^nX_k$ and $W_n=\sum_{k=1}^n\mathbb E[X_k^2\mid\mathcal F_{k-1}]$. For all $\tau\ge0$ and $\sigma^2\ge0$,
--   $$\mathbb P\{|Y_n|\ge\tau\text{ and }W_n\le\sigma^2\}\le2\exp\Big(-\frac{\tau^2/2}{\sigma^2+R\tau/3}\Big).$$
--   If moreover $W_n\le\sigma^2$ holds, then for every integer $K\ge1$ and every $\delta\in(0,1)$, with probability at least $1-\delta$,
--   $$|Y_n|\le\sqrt{8\max\Big\{W_n,\frac{\sigma^2}{2^K}\Big\}\log\frac{2K}\delta}+\frac43R\log\frac{2K}\delta.$$
--
--   The second bound has a variance term that adapts to the realized $W_n$. It is the concentration tool applied to the martingale term of the Q-learning recursion, where the variance depends on the iterates.
--
--   **Formalization Note** The one-sided inequality behind (56) is the published `BestBothWorlds.SAO.freedman`, a reference item of this mission.
--
--   Differences from the source:
--   - generalization: conditioning on {X_j}_{j<k} → any filtration to which X_k is adapted; reason: the natural filtration specializes it, and Appendix B applies it by conditioning on V_{i−1},…,V_0
--   - generalization: |X_k| ≤ R for all k ≥ 1, surely → |X_k| ≤ R almost surely for 1 ≤ k ≤ n; reason: the page's hypothesis implies this one
--   - generalization: W_n ≤ σ² deterministically → W_n ≤ σ² almost surely; reason: the page's hypothesis implies this one
--   - reading: (56) leaves the range of τ unstated → 0 ≤ τ; reason: at τ < 0 the event ignores |Y_n|; the page's use and proof have τ ≥ 0
--   - encoding: R ≥ 0 is forced by |X_k| ≤ R for all k ≥ 1 → the hypothesis 0 ≤ R; reason: with the bound assumed only up to n, the case n = 0 needs it; it excludes nothing on the page
-- source:
--   Li, Cai, Chen, Wei & Chi, Is Q-Learning Minimax Optimal? A Tight Sample Complexity Analysis, arXiv:2102.06548v4 (https://arxiv.org/abs/2102.06548v4), Theorem 6, pp.18–19, (56)–(57)

import Mathlib

open MeasureTheory

namespace TightQLearning

/-- Theorem 6, Freedman's inequality (Li, Cai, Chen, Wei & Chi, arXiv:2102.06548v4, pp.18–19): (56)
and the peeled form (57), on a filtration, with `Y_n = ∑_{k=1}^n X_k` and
`W_n = ∑_{k=1}^n E_{k−1}[X_k²]`. "`W_n ≤ σ²` deterministically" is taken almost surely.

**Formalization Note.** (56) is stated for `τ ≥ 0`, which the page leaves implicit. The page's
`E_{k−1}` is conditioning on `{X_j}_{j<k}`, the special case of the natural filtration. `0 ≤ R` is
automatic on the page, where the bound holds for all `k ≥ 1`. -/
theorem theorem_6 {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (n : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hadapted : ∀ k ∈ Finset.Icc 1 n, Measurable[ℱ k] (X k))
    (hmds : ∀ k ∈ Finset.Icc 1 n, μ[X k | ℱ (k - 1)] =ᵐ[μ] 0)
    (hbd : ∀ k ∈ Finset.Icc 1 n, ∀ᵐ ω ∂μ, |X k ω| ≤ R) :
    (∀ τ σsq : ℝ, 0 ≤ τ → 0 ≤ σsq →
      μ.real {ω | τ ≤ |∑ k ∈ Finset.Icc 1 n, X k ω| ∧
          ∑ k ∈ Finset.Icc 1 n, μ[fun ω' => X k ω' ^ 2 | ℱ (k - 1)] ω ≤ σsq} ≤
        2 * Real.exp (-(τ ^ 2 / 2) / (σsq + R * τ / 3))) ∧
    (∀ σsq : ℝ, 0 ≤ σsq →
      (∀ᵐ ω ∂μ, ∑ k ∈ Finset.Icc 1 n, μ[fun ω' => X k ω' ^ 2 | ℱ (k - 1)] ω ≤ σsq) →
      ∀ K : ℕ, 1 ≤ K → ∀ δ : ℝ, 0 < δ → δ < 1 →
        1 - δ ≤ μ.real {ω | |∑ k ∈ Finset.Icc 1 n, X k ω| ≤
          Real.sqrt (8 * max (∑ k ∈ Finset.Icc 1 n, μ[fun ω' => X k ω' ^ 2 | ℱ (k - 1)] ω)
              (σsq / 2 ^ K) * Real.log (2 * K / δ)) +
            4 / 3 * R * Real.log (2 * K / δ)}) := by sorry

end TightQLearning
