-- Prove2me | Theorems.Thm_RobustMultitask_Estimator_proposition_5
-- name    : RobustMultitask.Estimator.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:34:07.458013+00:00
-- url     : https://prove2.me/theorems/0153cd05-92ea-49f3-a2da-da1280d04d91
-- title:
--   Proposition 5 (with the coefficient 4C₀ established by its proof, p. 43) — high-probability ℓ1 error bound for the RMEstimator
-- statement:
--   Work in the fixed-design multitask linear model: $N$ tasks, task $j$ with $n_j$ observations, design matrices $X^j\in\mathbb R^{n_j\times d}$ standardized as in (1), parameters $\beta^j=\beta^\dagger+\delta^j$ with $\|\delta^j\|_0\le s$, responses $Y^j=X^j\beta^j+\epsilon^j$ with mutually independent mean-zero $\sigma_j$-subgaussian noise, and Assumption 1: $\lambda_{\min}(X^{j\top}X^j/n_j)\ge\psi>0$ for every task. Let $\widehat\beta^j_{\mathrm{RM}}$ be an output of Algorithm 1 (the LASSO step centred at the componentwise trimmed mean $\widehat\beta^\dagger_{\mathrm{RM}}$ of the OLS estimates), with trimming level $\omega=\zeta+\eta$ and regularization $\lambda_j$.
--
--   The paper states (p. 17): *Under Assumption 1, the estimator $\widehat\beta^j_{RM}$ satisfies*
--   $$\|\widehat\beta^j_{RM}-\beta^j\|_1\le\frac{6\lambda_js}{\zeta\psi}+C_0d(3\zeta+4\eta)\max_{i\in[N]}\sqrt{\frac{\sigma_i^2}{n_i\psi}\log\Big(\frac3\eta\Big)}$$
--   *with at least probability $1-\big(3d\exp(-N\eta^2/9)+2d\exp(-\lambda_j^2n_j/(32\sigma_j^2))\big)$, for any $\lambda_j>0$, $0<\eta\le1/2-1/C_0-\zeta$ and $0<\zeta<1/2$ with some constant $C_0>2$.*
--
--   The statement formalized here is: for every constant $C_0>2$, every $0<\zeta<1/2$, every $0<\eta\le 1/2-1/C_0-\zeta$, every task $j$ and every $\lambda_j>0$,
--   $$\|\widehat\beta^j_{\mathrm{RM}}-\beta^j\|_1\ \le\ \frac{6\lambda_js}{\zeta\psi}+4C_0\,d\,(3\zeta+4\eta)\max_{i\in[N]}\sqrt{\frac{\sigma_i^2}{n_i\psi}\log\frac{3}{\eta}}$$
--   with probability at least
--   $$1-\Big(3d\exp\Big(-\frac{N\eta^2}{9}\Big)+2d\exp\Big(-\frac{\lambda_j^2n_j}{32\sigma_j^2}\Big)\Big).$$
--
--   This is the paper's main error bound for the robust multitask estimator; Theorem 1 and the data-poor results follow by choosing the hyperparameters.
--
--   **Formalization Note** The printed statement has $C_0$ in place of $4C_0$; the proof on pp. 41–43 establishes the bound with $4C_0$ (final display of p. 43 combined with (16)), and that is what is stated here. The constant $C_0$ is universally quantified, and the trimming level is fixed to $\omega=\zeta+\eta$, as in Proposition 4 on which the proof rests. The conclusion is that the outer probability of the failure event (strict $>$) is at most $3d\exp(-N\eta^2/9)+2d\exp(-\lambda_j^2n_j/(32\sigma_j^2))$, which needs no measurability of the estimator. `βhat ω` is an arbitrary choice of global LASSO minimizer at each sample point (under Assumption 1 the minimizer is unique). The model requires $n_j\ge1$ and $\sigma_j>0$; $\lambda_{\min}$ is in Rayleigh-quotient form; $\log$ is the natural logarithm; the trimmed mean removes $\lfloor N\omega\rfloor$ values from each end.
-- source:
--   Xu & Bastani, Multitask Learning and Bandits via Robust Statistics, arXiv:2112.14233v5, p. 17, Proposition 5 (proof pp. 41–43; coefficient 4C₀ from the final display of p. 43 and eq. (16))

import Mathlib
import Definitions.Def_RobustMultitask_Estimator_VectorNotation
import Definitions.Def_RobustMultitask_Estimator_TrimmedMean
import Definitions.Def_RobustMultitask_Estimator_Model
import Definitions.Def_RobustMultitask_Estimator_Algorithm

namespace RobustMultitask.Estimator

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Proposition 5, p. 17, with the coefficient `4C₀` that its proof establishes (p. 43). In the
fixed-design multitask model under Assumption 1, for every `C₀ > 2`, `0 < ζ < 1/2`,
`0 < η ≤ 1/2 − 1/C₀ − ζ`, task `j` and `λ_j > 0`, every output `β̂ʲ_RM` of Algorithm 1 with
trimming level `ω = ζ + η` satisfies
`‖β̂ʲ_RM − βʲ‖₁ ≤ 6λ_j s/(ζψ) + 4C₀ d (3ζ + 4η) max_{i∈[N]} √(σ_i²/(n_iψ) log(3/η))`
with probability at least `1 − (3d exp(−Nη²/9) + 2d exp(−λ_j² n_j/(32σ_j²)))`. `βhat ω` is any
choice of LASSO minimizer at each sample point. -/
theorem proposition_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N d : ℕ} (n : Fin N → ℕ) (X : (j : Fin N) → Matrix (Fin (n j)) (Fin d) ℝ)
    (β : Fin N → Fin d → ℝ) (βdag : Fin d → ℝ) (s : ℕ) (σ : Fin N → ℝ≥0)
    (ε : (j : Fin N) → Fin (n j) → Ω → ℝ)
    (hmodel : IsMultitaskModel P n X β βdag s σ ε) (ψ : ℝ) (hA1 : Assumption1 n X ψ)
    (C₀ ζ η : ℝ) (hC₀ : 2 < C₀) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 2 - 1 / C₀ - ζ)
    (j : Fin N) (lam : ℝ) (hlam : 0 < lam) (βhat : Ω → Fin d → ℝ)
    (hβhat : ∀ ω, IsRMEstimate n X (fun k => response X β ε k ω) (ζ + η) lam j (βhat ω)) :
    P {ω | 6 * lam * s / (ζ * ψ)
            + 4 * C₀ * d * (3 * ζ + 4 * η)
              * (⨆ i, Real.sqrt ((σ i : ℝ) ^ 2 / ((n i : ℝ) * ψ) * Real.log (3 / η)))
          < l1 (βhat ω - β j)}
      ≤ ENNReal.ofReal (3 * d * Real.exp (-((N : ℝ) * η ^ 2) / 9)
          + 2 * d * Real.exp (-(lam ^ 2 * (n j : ℝ)) / (32 * (σ j : ℝ) ^ 2))) := by sorry

end RobustMultitask.Estimator
