-- Prove2me | Theorems.Thm_PoissonDepTrials_SecondOrder_bound_5_9
-- name    : PoissonDepTrials.SecondOrder.bound_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:52:39.880313+00:00
-- url     : https://prove2.me/theorems/a438ebfc-563f-4dbd-9ceb-aa72d62995aa
-- title:
--   (5.9), p. 545 — |Eh(W) − 𝒫_λh + (Σp_i²)𝒫_λU_λh| ≤ 24λ^{−1}Σp_i³ + 96λ^{−1}Σ_iΣ_{j≠i} p_i²p_j²/λ^{(i)}
-- statement:
--   Let $X_1,\dots,X_n$ ($n\ge2$) be independent Bernoulli trials with $p_i=P(X_i=1)$, $\lambda=\sum_ip_i>0$, $\max_ip_i\le\lambda/2$, and $\lambda^{(i)}=\sum_{j\ne i}p_j$. For every $h$ with $|h|\le1$,
--   $$\Bigl|Eh(W)-\mathscr P_\lambda h+\Bigl(\sum_{i=1}^np_i^2\Bigr)\mathscr P_\lambda U_\lambda h\Bigr|\le24\lambda^{-1}\sum_{i=1}^np_i^3+96\lambda^{-1}\sum_{i=1}^n\sum_{j\ne i}\frac{p_i^2p_j^2}{\lambda^{(i)}}.$$
--
--   This is the error bound of the second-order expansion before the final averaging step; Theorem 5.1 follows from it and the Jensen chain.
--
--   **Formalization Note** The page writes the right side as $24\lambda^{-1}nEp_I^3+96\lambda^{-1}n(n-1)E(\lambda^*)^{-1}p_I^2p_J^2$ with random indices $(I,J)$ uniform on ordered pairs of distinct indices and $\lambda^*=\lambda^{(I)}$; the index form stated here is the same quantity. $\lambda>0$ is added (under $\max p_i\le\lambda/2$ it makes $\lambda^{(i)}\ge\lambda/2>0$, so no division by $0$ occurs). The trials are a sequence $X:\mathbb N\to\Omega\to\mathbb N$ with $X_i\in\{0,1\}$ almost surely and $X_i\equiv0$ for $i=0$ and $i>n$, the paper's own padding convention (p. 535); constants generate the trivial $\sigma$-algebra, so independence of the padded family is independence of $X_1,\dots,X_n$.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 545, proof of Theorem 5.1, (5.9)

import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

open MeasureTheory ProbabilityTheory Finset

namespace PoissonDepTrials.SecondOrder

/-- (5.9), proof of Theorem 5.1, p. 545, in index form:
`|Eh(W) − 𝒫_λh + (Σp_i²)𝒫_λU_λh| ≤ 24λ^{−1}Σ_i p_i³ + 96λ^{−1}Σ_i Σ_{j≠i} p_i²p_j²/λ^{(i)}`. -/
theorem bound_5_9 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (hind : iIndepFun (fun i => X i) P)
    (h : ℕ → ℝ) (hh : ∀ k, |h k| ≤ 1) (hn : 2 ≤ n)
    (hpbar : ∀ i ∈ Finset.Icc 1 n, prob P X i ≤ lam P n X / 2) (hlam : 0 < lam P n X) :
    |∫ ω, h (W n X ω) ∂P - poissonExp (lam P n X) h +
        (∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2) * poissonExp (lam P n X) (stU (lam P n X) h)| ≤
      24 * (lam P n X)⁻¹ * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 3 +
        96 * (lam P n X)⁻¹ * ∑ i ∈ Finset.Icc 1 n,
          ∑ j ∈ (Finset.Icc 1 n).filter (fun j : ℕ => j ≠ i),
            prob P X i ^ 2 * prob P X j ^ 2 / lamExcept P n X i := by sorry

end PoissonDepTrials.SecondOrder
