-- Prove2me | Theorems.Thm_PLIAG_eq_C_15
-- name    : PLIAG.eq_C_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:27:35.036076+00:00
-- url     : https://prove2.me/theorems/1bc180a4-e8dc-49fe-b8b1-11fca5f3e0f3
-- title:
--   (C.15), p.26 — the rate at $\alpha=\alpha_0$
-- statement:
--   Let $\mu>0$, $L>0$, $\tau\in\mathbb N$, let $\ell$ be monotonically increasing with $\ell(1)=1$, let $\alpha_0$ be given by (4.5), and write $Q:=L/\mu$ for the condition number. Then
--
--   1. $\displaystyle\frac{1}{1+\alpha_0\mu}=\Big(1+\frac{1}{\ell(\tau+1)Q}\Big)^{-\frac1{\tau+1}}$;
--   2. $\displaystyle\Big(1+\frac{1}{\ell(\tau+1)Q}\Big)^{-\frac1{\tau+1}}=\Big(1-\frac{1}{1+\ell(1+\tau)Q}\Big)^{\frac1{\tau+1}}$;
--   3. for every $k\ge0$, $\displaystyle\Big(\frac{1}{1+\alpha_0\mu}\Big)^k=\Big(1-\frac{1}{1+\ell(\tau+1)Q}\Big)^{\frac{k}{\tau+1}}$;
--   4. for every $k\ge0$, by Bernoulli's inequality,
--   $$
--   \Big(\frac{1}{1+\alpha_0\mu}\Big)^k\ \le\ \Big(1-\frac{1}{[1+\ell(\tau+1)Q](\tau+1)}\Big)^k .
--   $$
--
--   Combined with (4.7), this gives the explicit rate (4.10) of Theorem 4.2 in terms of the condition number and the delay.
--
--   Differences from the source:
--   - generalization: L = max_{k≥0} Σ_{j∈J_k} L_j → any real L > 0; reason: the paper’s L is positive, so the statement specializes to it
--   - encoding: ℓ monotonically increasing with ℓ(1) = 1 (introduced by B4 when τ > 0; ℓ(τ+1) = ℓ(1) = 1 when τ = 0) → ℓ : ℕ → ℝ with Monotone ℓ and ℓ 1 = 1 always; reason: when τ = 0 only ℓ(1) = 1 enters; ℓ(0) is never read and a monotone ℓ on the positive integers extends by ℓ(0) := ℓ(1)
--   - encoding: condition number Q := L/μ → L / μ (the letter Q names the constraint set); reason: notation only
-- source:
--   Zhang, Dai, Guo, Peng, Proximal-Like Incremental Aggregated Gradient Method with Linear Convergence under Bregman Distance Growth Conditions, arXiv:1711.01136v3, (C.15), proof of Theorem 4.2, p.26

import Mathlib
import Definitions.Def_PLIAG_alpha0

namespace PLIAG

/-- **(C.15): the rate at `α = α_0`** (Zhang–Dai–Guo–Peng, arXiv:1711.01136v3, proof of
Theorem 4.2, p.26). With `κ := L/μ` (the paper's condition number `Q`):
1. `1/(1 + α_0 μ) = (1 + 1/(ℓ(τ+1)κ))^{−1/(τ+1)}`;
2. `(1 + 1/(ℓ(τ+1)κ))^{−1/(τ+1)} = (1 − 1/(1 + ℓ(1+τ)κ))^{1/(τ+1)}`;
3. `(1/(1 + α_0 μ))^k = (1 − 1/(1 + ℓ(τ+1)κ))^{k/(τ+1)}` for all `k`;
4. `(1/(1 + α_0 μ))^k ≤ (1 − 1/([1 + ℓ(τ+1)κ](τ+1)))^k` for all `k` (Bernoulli).

**Formalization Note.** `κ` is written `L / μ` (the letter `Q` names the constraint set
elsewhere); `L > 0` is any real (in the paper `L = max_k Σ_{j∈J_k} L_j`), `μ > 0`, `ℓ` monotone
with `ℓ(1) = 1`. Real powers are `Real.rpow`. -/
theorem eq_C_15 (μ L : ℝ) (ℓ : ℕ → ℝ) (τ : ℕ) (hμ : 0 < μ) (hL : 0 < L)
    (hℓm : Monotone ℓ) (hℓ1 : ℓ 1 = 1) :
    1 / (1 + alpha0 μ L ℓ τ * μ) =
        (1 + 1 / (ℓ (τ + 1) * (L / μ))) ^ (-(1 : ℝ) / ((τ : ℝ) + 1)) ∧
    (1 + 1 / (ℓ (τ + 1) * (L / μ))) ^ (-(1 : ℝ) / ((τ : ℝ) + 1)) =
        (1 - 1 / (1 + ℓ (1 + τ) * (L / μ))) ^ ((1 : ℝ) / ((τ : ℝ) + 1)) ∧
    (∀ k : ℕ, (1 / (1 + alpha0 μ L ℓ τ * μ)) ^ k =
        (1 - 1 / (1 + ℓ (τ + 1) * (L / μ))) ^ ((k : ℝ) / ((τ : ℝ) + 1))) ∧
    (∀ k : ℕ, (1 / (1 + alpha0 μ L ℓ τ * μ)) ^ k ≤
        (1 - 1 / ((1 + ℓ (τ + 1) * (L / μ)) * ((τ : ℝ) + 1))) ^ k) := by sorry

end PLIAG
