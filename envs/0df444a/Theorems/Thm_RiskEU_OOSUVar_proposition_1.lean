-- Prove2me | Theorems.Thm_RiskEU_OOSUVar_proposition_1
-- name    : RiskEU.OOSUVar.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:08.891308+00:00
-- url     : https://prove2.me/theorems/9fba19c2-7536-45b7-96fa-951026bd081b
-- title:
--   Proposition 1, pp. 14–15 — closed-form out-of-sample utility variance of the shrinkage portfolio ŵ*(κ)
-- statement:
--   Let $N$ stocks have excess-return mean $\mu$ and positive-definite covariance $\Sigma$, let the investor have risk aversion $\gamma>0$, and let $\sigma_g^2,\psi^2$ be computed from $\mu,\Sigma$ by (6)–(7). Suppose Assumption 1 ($N\ge2$, $T>N+7$) and Assumption 2 ($r_1,\dots,r_T$ independent, each $\mathcal N(\mu,\Sigma)$) hold, and let $\hat w^\star(\kappa)$ be the shrinkage portfolio (11) built from the sample mean and the $1/T$ sample covariance, with $\kappa\in[0,1]$. Then the out-of-sample utility $U(\hat w^\star(\kappa))=\hat w^\star(\kappa)^\top\mu-\frac\gamma2\hat w^\star(\kappa)^\top\Sigma\hat w^\star(\kappa)$ has a finite second moment and
--
--   $$\mathbb V[U(\hat w^\star(\kappa))]=\mathbb V[U(\hat w_g)]+\Delta(\kappa),\qquad \mathbb V[U(\hat w_g)]=\frac{\sigma_g^2\psi^2}{T-N-1}+\frac{\gamma^2\sigma_g^4(N-1)(T-2)}{2(T-N-1)^2(T-N-3)},$$
--
--   where $\Delta(\kappa)=a_1\kappa^4+a_2\kappa^3+a_3\kappa^2+a_4\kappa$ with the coefficients (16)–(19):
--
--   $$a_1=\frac{1}{2\gamma^2}\frac{T^2(T-2)C(T,N,\psi^2)}{(T-N)^2(T-N-1)^2(T-N-2)(T-N-3)^2(T-N-5)(T-N-7)},\qquad a_2=-\frac{2\psi^2}{\gamma^2}\frac{T^2(T-2)(T+N-3+2T\psi^2)}{(T-N)(T-N-1)^2(T-N-3)(T-N-5)},$$
--
--   $$a_3=\frac{\psi^2}{\gamma^2}\frac{2T(N+1)+T^2(T-N-3+2(T-N)\psi^2)}{(T-N)(T-N-1)^2(T-N-3)}+\sigma_g^2\frac{T(T-2)(T+N-3)(T\psi^2+N-1)}{(T-N)(T-N-1)^2(T-N-3)(T-N-5)},\qquad a_4=-2\sigma_g^2\psi^2\frac{T(T-2)}{(T-N-1)^2(T-N-3)},$$
--
--   and $C(T,N,\psi^2)$ is the explicit polynomial printed on p. 15. Moreover, the out-of-sample utility of the sample GMV portfolio $\hat w_g$ has a finite second moment and its variance is exactly $\mathbb V[U(\hat w_g)]$ above (14).
--
--   The result shows that the risk of the out-of-sample utility of the shrinkage portfolio depends only on $\kappa,\gamma,N,T,\sigma_g^2$ and $\psi^2$. It is the input of the paper's mean-risk analysis of the shrinkage intensity (Corollary 1, Propositions 2 and 4).
--
--   **Formalization Note.** The left-hand sides are `ProbabilityTheory.variance` of the out-of-sample utility under the sampling measure, not the formula under another name; the `MemLp … 2` conjuncts assert that these variances exist (the paper notes that $T>N+7$ guarantees this, p. 12), since Lean's `variance` is $0$ for a variable without a second moment. $\sigma_g^2$ and $\psi^2$ are computed from $\mu,\Sigma$, never taken as parameters. $\hat\Sigma$ is normalised by $1/T$ as in (9). Matrix inversion uses Mathlib's convention $A^{-1}=0$ for singular $A$, which is harmless because $\hat\Sigma$ is almost surely invertible when $T>N$.
-- source:
--   Lassance, Martín-Utrera, Simaan, The Risk of Expected Utility under Parameter Uncertainty, SSRN 3855546 (version dated August 18, 2023), Proposition 1, (13)–(19), pp. 14–15

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting

namespace RiskEU.OOSUVar

open MeasureTheory ProbabilityTheory Matrix

theorem proposition_1 {N T : ℕ} (M : Market N) (hM : M.Standing T)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin T → Ω → EuclideanSpace ℝ (Fin N)) (hr : M.IsGaussianSample P r)
    (κ : ℝ) (hκ : κ ∈ Set.Icc (0 : ℝ) 1) :
    MemLp (fun ω => M.U (M.wShrink κ (sampleData r ω))) 2 P ∧
    variance (fun ω => M.U (M.wShrink κ (sampleData r ω))) P =
      varGMV M.gamma T N M.sigmaG2 M.psi2 + Delta M.gamma T N M.sigmaG2 M.psi2 κ ∧
    MemLp (fun ω => M.U (wHatG (sampleData r ω))) 2 P ∧
    variance (fun ω => M.U (wHatG (sampleData r ω))) P =
      varGMV M.gamma T N M.sigmaG2 M.psi2 := by sorry

end RiskEU.OOSUVar
