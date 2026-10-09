-- Prove2me | Theorems.Thm_PoissonDepTrials_SecondOrder_theorem_5_1
-- name    : PoissonDepTrials.SecondOrder.theorem_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:52:53.541594+00:00
-- url     : https://prove2.me/theorems/419741aa-4c3d-43ba-9ecd-f98e305133fc
-- title:
--   Theorem 5.1, p. 544 — for independent trials with max p_i ≤ λ/2, |Eh(W) − 𝒫_λh + (Σp_i²)𝒫_λU_λh| ≤ (24 + 96√2)λ^{−1}Σp_i³
-- statement:
--   Let $X_1,\dots,X_n$ be independent Bernoulli random variables with $p_i=P(X_i=1)$, let $W=\sum_{i=1}^nX_i$ and $\lambda=\sum_{i=1}^np_i$, and suppose $\bar p=\max_{1\le i\le n}p_i\le\lambda/2$ and $n\ge2$. For a function $h$ on the nonnegative integers let $\mathscr P_\lambda h=e^{-\lambda}\sum_{k\ge0}h(k)\lambda^k/k!$ be its Poisson($\lambda$) expectation, $S_\lambda h$ the solution of the Stein equation $wf(w)-\lambda f(w+1)=h(w)-\mathscr P_\lambda h$ ($w\ge1$), and $U_\lambda h(w)=S_\lambda h(w+2)-S_\lambda h(w+1)$. Then for every $h$ with $|h|\le1$,
--   $$\Bigl|Eh(W)-\mathscr P_\lambda h+\Bigl(\sum_{i=1}^np_i^2\Bigr)\mathscr P_\lambda U_\lambda h\Bigr|\le\bigl(24+96\sqrt2\bigr)\lambda^{-1}\sum_{i=1}^np_i^3.$$
--
--   The theorem is a second-order Poisson expansion: the first-order error of Le Cam's bound is of order $\sum p_i^2$, and after subtracting the explicit correction $-(\sum p_i^2)\mathscr P_\lambda U_\lambda h$ the remainder is of order $\lambda^{-1}\sum p_i^3$, uniformly over $|h|\le1$.
--
--   **Formalization Note** The page says "$C\lambda^{-1}\sum p_i^3$ where $C$ is an absolute constant not greater than $24+96(2)^{1/2}$"; since the right side is nonnegative this is stated with $C=24+96\sqrt2$. $\bar p\le\lambda/2$ is written as $p_i\le\lambda/2$ for every $i$. No $\lambda>0$ is assumed: at $\lambda=0$ all $p_i=0$, $W=0$ almost surely and both sides vanish. The trials are a sequence $X:\mathbb N\to\Omega\to\mathbb N$ with $X_i\in\{0,1\}$ almost surely and $X_i\equiv0$ for $i=0$ and $i>n$, the paper's own padding convention (p. 535); constants generate the trivial $\sigma$-algebra, so independence of the padded family is independence of $X_1,\dots,X_n$.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 544, Theorem 5.1, (5.7)

import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

open MeasureTheory ProbabilityTheory Finset

namespace PoissonDepTrials.SecondOrder

/-- Theorem 5.1, (5.7), p. 544: if `X_1, …, X_n` are independent Bernoulli trials with
`max_i p_i ≤ λ/2`, then for `|h| ≤ 1` and `n ≥ 2`,
`|Eh(W) − 𝒫_λh + (Σ_{i=1}^n p_i²)𝒫_λU_λh| ≤ Cλ^{−1}Σ_{i=1}^n p_i³` with `C = 24 + 96·2^{1/2}`. -/
theorem theorem_5_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (hind : iIndepFun (fun i => X i) P)
    (h : ℕ → ℝ) (hh : ∀ k, |h k| ≤ 1) (hn : 2 ≤ n)
    (hpbar : ∀ i ∈ Finset.Icc 1 n, prob P X i ≤ lam P n X / 2) :
    |∫ ω, h (W n X ω) ∂P - poissonExp (lam P n X) h +
        (∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2) * poissonExp (lam P n X) (stU (lam P n X) h)| ≤
      (24 + 96 * Real.sqrt 2) * (lam P n X)⁻¹ * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 3 := by sorry

end PoissonDepTrials.SecondOrder
