-- Prove2me | Theorems.Thm_SupplyChainTheory_risk_pooling
-- name    : SupplyChainTheory.risk_pooling
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:09:25.603079+00:00
-- url     : https://prove2.me/theorems/dfb6abc3-c6c0-42af-8595-788008172ea5
-- title:
--   Theorem 7.1 (risk pooling): the centralized system costs no more than the decentralized one, $g^*_C \le g^*_D$
-- statement:
--   **Theorem 7.1.** $N$ distribution centers face normally distributed per-period demands
--   $D_i \sim N(\mu_i, \sigma_i^2)$ with correlation coefficients $\rho_{ij}$, each following a
--   base-stock policy with zero lead time, holding cost $h > 0$ and backorder cost $p > 0$ per unit
--   per period. The optimal expected cost of the decentralized system is the sum of the $N$
--   optimal newsvendor costs, $g^*_D = \sum_i \min_S g_i(S)$ (Eq. 7.1); the centralized system
--   merges the centers into one facing the total demand, normal with mean $\sum_i \mu_i$ and
--   variance $\sum_i \sum_j \sigma_i \sigma_j \rho_{ij}$, and its optimal cost is
--   $g^*_C = \min_S g_0(S)$ (Eq. 7.2). Then
--
--   $$ g^*_C \;\le\; g^*_D. $$
--
--   This is the risk-pooling effect (Eppen 1979): pooled demand has a smaller standard deviation
--   than the sum of the individual ones, because variances, not standard deviations, add. The
--   book's proof evaluates both sides in closed form, $g^*_C = \eta\sigma_0$ and
--   $g^*_D = \eta\sum_i\sigma_i$ with $\eta = (p + h)\varphi(z_\alpha)$, and applies the
--   inequality $\sigma_0 \le \sum_i \sigma_i$.
--
--   **Formalization Note** The optimal costs are infima of the newsvendor cost over all
--   base-stock levels; the Gaussian laws are Mathlib's `gaussianReal` with variance clamped at
--   $0$, so a pooled variance that is not positive gives a degenerate demand at the mean. The
--   correlation matrix is assumed symmetric with unit diagonal and entries at most $1$.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 232, Sect. 7.2.5, Theorem 7.1; the model is Sect. 7.2.2-7.2.4 pp. 231-232, Eq. (7.1), (7.2); after Eppen (1979)

import Definitions.Def_SupplyChainTheory_flexibility

namespace SupplyChainTheory

theorem risk_pooling {N : ℕ} (h p : ℝ) (hh : 0 < h) (hp : 0 < p)
    (mu sig : Fin N → ℝ) (rho : Fin N → Fin N → ℝ)
    (hsig : ∀ i, 0 < sig i) (hrho : ∀ i j, rho i j ≤ 1) (hrho_diag : ∀ i, rho i i = 1)
    (hrho_symm : ∀ i j, rho i j = rho j i) :
    optNvCost h p
        (ProbabilityTheory.gaussianReal (∑ i, mu i) (Real.toNNReal (pooledVariance sig rho)))
      ≤ ∑ i, optNvCost h p
          (ProbabilityTheory.gaussianReal (mu i) (Real.toNNReal ((sig i) ^ 2))) := by sorry

end SupplyChainTheory
