-- Prove2me | Theorems.Thm_SLPEPricing_Regret_theorem_1
-- name    : SLPEPricing.Regret.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:23.985471+00:00
-- url     : https://prove2.me/theorems/e500da27-2653-449f-a8f9-e56c49638f1b
-- title:
--   Theorem 1 and Corollary 1, pp. 16–17, 25 — SLPE makes at most C₃ + 3 log₂ log T price changes, and on its concentration event has regret at most (C₁ + C₂ log log T)√T log T
-- statement:
--   Let the demand curve $d$, the optimal price $p^*$ and the constants $\kappa,K_1,c,\mu,\rho$ satisfy the standing hypotheses of Theorem 1: $d$ is three times continuously differentiable, non-increasing and nonnegative on $[0,1]$; $0<p^*<1$ is the unique maximiser of $r(p)=p\,d(p)$ on $[0,1]$; Assumption 1 holds with $\kappa>0$; $K_1$ bounds $|d^{(k)}|$ for $k\le3$; the gradient condition $|d'(p^*)|\ge(K_1/24+\kappa/4)\tfrac14+c/2$ holds with $c>0$; and
--   $$2>\mu\ge M=\frac1c\Big(\frac1{\rho^2}+\frac{K_1}6+\frac\kappa4\Big)+\frac{K_1}{12}+4\kappa,\qquad\rho>0 .$$
--   Then there are constants $C_1,C_2,C_3$, depending only on $d,p^*,\kappa,K_1,c,\mu,\rho$, such that for every argmax selector, every horizon $T\ge3$, every noise realisation $\epsilon$ and every pair selector, the SLPE policy run with parameters $(T,\mu,\rho)$ satisfies:
--   1. **(Corollary 1)** the number of price changes (5) is at most
--   $$LPC^{SLPE}(T)\le C_3+3\log_2(\log T);$$
--   2. **(Theorem 1)** if Assumption 2 and the concentration event $|\bar D_{n_i}(p^M_i)-d(p^M_i)|\le\Delta_i^2/\rho^2$ hold in every round whose estimate is used, the regret (4) is at most
--   $$\mathcal R^{SLPE}(T)\le\big(C_1+C_2\log(\log T)\big)\sqrt T\log T .$$
--
--   Together the two parts give the paper's main claim: a policy for an unknown non-parametric demand curve with regret $O(\sqrt T\log T\log\log T)$, within logarithmic factors of the $\sqrt T$ lower bound, while changing its price only $O(\log\log T)$ times.
--
--   **Formalization Note** The statement is pathwise. Regret (4) is written without an expectation on the page; the page's probabilistic argument relies on a per-round failure probability $1/T^2$ that is false for $\sigma\ge1$ (see the Hoeffding milestone), and Assumption 2 has probability zero under i.i.d. continuous noise. So the regret bound is stated for every realisation on which Assumption 2 and the concentration event hold, and the price-change bound for every realisation. The paper's $\log(\log(T/(2\mu\rho^4\log T)))$ is replaced by $\log(\log T)$, equivalent up to the constants for $T\ge3$. Corollary 1's printed bound $3\tilde C+3\log(\log(T/(2\mu\rho^4\log T)))$ is false with natural logarithms (with $d(p)=1-p$, $\mu=1.9$, $\rho=1$, zero noise and $T=10^6$, SLPE makes 19 price changes against a bound of 15.8, and no constant can rescue the coefficient 3 in front of $\ln\ln T$), so it is posed with $\log_2$, the base its derivation needs. Assumption 1 and $K_1$ are imposed on $[-1,2]$ and $p^*<1$ is added (see the Model's note). The constants are quantified before $T$, the noise and the selectors, so they cannot depend on them. Periods are 0-based, rounds 1-based. Theorem 2 (the relaxed Assumption 2A) is not part of this statement.
-- source:
--   Perakis & Singhvi, Dynamic Pricing with Unknown Non-Parametric Demand and Limited Price Changes, SSRN 3336949 (PDF of 2020-07-03), pp. 16–17, Theorem 1; p. 25, Corollary 1

import Mathlib
import Definitions.Def_SLPEPricing_Regret_Model

namespace SLPEPricing.Regret

/-- Theorem 1 (pp. 16–17) and Corollary 1 (p. 25). Under the standing hypotheses there are
constants `C₁, C₂, C₃`, independent of `T`, the noise realisation and the selectors, such that
for every argmax selector, every `T ≥ 3`, every noise realisation `ε` and pair selector `sel`:
SLPE makes at most `C₃ + 3 log₂(log T)` price changes, and, if Assumption 2 and the
concentration event hold in every used round, its regret is at most
`(C₁ + C₂ log(log T)) √T log T`. -/
theorem theorem_1 (d : ℝ → ℝ) (pstar κ K₁ c μ ρ : ℝ) (h : Standing d pstar κ K₁ c μ ρ) :
    ∃ C₁ C₂ C₃ : ℝ, ∀ amax : (ℝ → ℝ) → ℝ → ℝ → ℝ, IsArgmaxSelector amax →
      ∀ T : ℕ, 3 ≤ T → ∀ (ε : ℕ → ℝ) (sel : ℕ → ℕ × ℕ × ℕ × ℕ),
        (lpc d μ ρ amax sel ε T : ℝ) ≤ C₃ + 3 * Real.logb 2 (Real.log (T : ℝ)) ∧
        (Assumption2 μ ρ T sel ε → Concentration d μ ρ amax sel ε T →
          regret d pstar μ ρ amax sel ε T ≤
            (C₁ + C₂ * Real.log (Real.log (T : ℝ))) * Real.sqrt (T : ℝ) * Real.log (T : ℝ)) := by sorry

end SLPEPricing.Regret
