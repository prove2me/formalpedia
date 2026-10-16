-- Prove2me | Theorems.Thm_SubsetShrink_L1_theorem_3
-- name    : SubsetShrink.L1.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:42.938221+00:00
-- url     : https://prove2.me/theorems/930b2218-994b-46db-9645-fbb6498025db
-- title:
--   Theorem 3, p. 16 — slow and fast oracle inequalities for ℓ1-regularized best subsets
-- statement:
--   Let $X$ have unit Euclidean-norm columns, $y=f^*+\epsilon$, $\sigma>0$, $1\le k\le p$, and $0<\delta_0\le1$. Let $\hat\beta_1$ be any minimizer of the $\ell_1$-regularized best subset objective over $B_0(k)$. For every $\beta\in B_0(k)$, Theorem 3 gives three bounds.
--
--   1. If $\lambda=2\sigma\sqrt{2\log(2p)}+2\sigma\sqrt{2\log(1/\delta_0)}$ and $\epsilon\in\mathcal H$, then
--      $$\|f^*-X\hat\beta_1\|_2^2\le\|f^*-X\beta\|_2^2+2\lambda\|\beta\|_1.$$
--   2. If $\lambda\ge(8+2\sqrt2)\sigma\sqrt{\log(2p)}$ and $\epsilon\in\mathcal F$, a positive universal $C_A$ gives
--      $$\|f^*-X\hat\beta_1\|_2^2\le C_A[\|f^*-X\beta\|_2^2+\lambda\|\beta\|_1+\sigma^2\log(1/\delta_0)].$$
--   3. If $\lambda\ge0$ and $\epsilon\in\mathcal G_{2k}$, a positive universal $C_B$ gives
--      $$\|f^*-X\hat\beta_1\|_2^2\le C_B[\|f^*-X\beta\|_2^2+\sigma^2k\log(ep/k)+\lambda^2k/\gamma_{2k}^2+\sigma^2\log(1/\delta_0)].$$
--
--   These are the paper's exact first slow-rate bound, second slow-rate bound, and fast-rate bound on their respective noise events.
--
--   **Formalization Note** $C_A,C_B$ precede all data and dimensions. The infima are expressed by a bound for every sparse comparator. In the fast branch $\gamma_{2k}>0$ or $\lambda=0$ is assumed so the quotient has its intended meaning under Lean's total division. The deterministic event $\mathcal G_{2k}$ uses the printed event definition.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 16, Theorem 3; proof B.6, pp. 42–43

import Mathlib
import Definitions.Def_SubsetShrink_L1_Model

namespace SubsetShrink.L1

/-- Theorem 3, p. 16. `CA` and `CB` are universal constants, quantified
before every dimension and model parameter. The fast branch pins `γ₂ₖ > 0`
unless `lam = 0`, to keep Lean's real division faithful to the paper. -/
theorem theorem_3 :
    ∃ CA CB : ℝ, 0 < CA ∧ 0 < CB ∧
      ∀ {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
        (fstar ε : Fin n → ℝ) (k : ℕ) (σ δ0 lam : ℝ)
        (βhat : Fin p → ℝ),
        SubsetShrink.Events.UnitCols X → 1 ≤ k → k ≤ p → 0 < σ → 0 < δ0 → δ0 ≤ 1 →
        IsL1BestSubset X (fun i => fstar i + ε i) k lam βhat →
        ∀ β : Fin p → ℝ, SubsetShrink.Events.l0 β ≤ k →
          (lam = 2 * σ * Real.sqrt (2 * Real.log (2 * (p : ℝ))) +
              2 * σ * Real.sqrt (2 * Real.log (1 / δ0)) →
            ε ∈ SubsetShrink.Events.H X σ δ0 →
              predictionError X fstar βhat ≤
                predictionError X fstar β + 2 * lam * SubsetShrink.Events.l1 β) ∧
          ((8 + 2 * Real.sqrt 2) * σ *
              Real.sqrt (Real.log (2 * (p : ℝ))) ≤ lam →
            ε ∈ SubsetShrink.Events.F X σ δ0 →
              predictionError X fstar βhat ≤
                CA * (predictionError X fstar β + lam * SubsetShrink.Events.l1 β +
                  σ ^ 2 * Real.log (1 / δ0))) ∧
          (0 ≤ lam → (0 < SubsetShrink.L2.gam X (2 * k) ∨ lam = 0) →
            ε ∈ SubsetShrink.Events.G X σ δ0 (2 * k) →
              predictionError X fstar βhat ≤
                CB * (predictionError X fstar β +
                  σ ^ 2 * (k : ℝ) * Real.log (Real.exp 1 * (p : ℝ) / k) +
                  lam ^ 2 * (k : ℝ) / (SubsetShrink.L2.gam X (2 * k)) ^ 2 +
                  σ ^ 2 * Real.log (1 / δ0))) := by sorry

end SubsetShrink.L1
