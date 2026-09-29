-- Prove2me | Theorems.Thm_PolyakJuditsky_Averaging_linear_sa_asymptotic_normality
-- name    : PolyakJuditsky.Averaging.linear_sa_asymptotic_normality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T23:39:59.650451+00:00
-- url     : https://prove2.me/theorems/e791f0fe-a30b-43d8-b473-5326c1d45c36
-- title:
--   Theorem 1(a) — asymptotic normality of averaged linear stochastic approximation
-- statement:
--   Let $A$ be a real $N\times N$ matrix whose eigenvalues all have positive real part, $b\in\mathbb R^N$, and $x^*$ the solution of $Ax^*=b$. Let the step sizes satisfy $\gamma_t>0$ ($t\ge1$), $\gamma_t\to0$ and $(\gamma_t-\gamma_{t+1})/\gamma_t=o(\gamma_t)$. On a filtered probability space $(\Omega,\mathcal F,(\mathcal F_t),P)$ let $(\xi_t)_{t\ge1}$ be an adapted, square-integrable martingale-difference sequence with $\sup_tE(|\xi_t|^2\mid\mathcal F_{t-1})<\infty$ a.s., satisfying the conditional Lindeberg condition
--   $$\lim_{C\to\infty}\limsup_{t\to\infty}E\bigl(|\xi_t|^2I(|\xi_t|>C)\mid\mathcal F_{t-1}\bigr)=0\ \text{in probability},$$
--   and $E(\xi_t\xi_t^T\mid\mathcal F_{t-1})\to S$ in probability for a symmetric positive definite $S$. For a nonrandom $x_0$ run algorithm (2),
--   $$x_t=x_{t-1}-\gamma_t(Ax_{t-1}-b+\xi_t),\qquad\bar x_t=\frac1t\sum_{i=0}^{t-1}x_i .$$
--   Then
--   $$\sqrt t\,(\bar x_t-x^*)\xrightarrow{D}N(0,V),\qquad V=A^{-1}S(A^{-1})^T.\tag{5}$$
--
--   The averaged estimate attains the covariance $A^{-1}S(A^{-1})^T$ of the optimal linear algorithm $x_t=x_{t-1}-t^{-1}A^{-1}y_t$ without knowledge of $A$. The proof of Theorem 2 applies this result to the linearised process with $A=G$.
--
--   **Formalization Note** Assumption 2.2 offers a constant step (condition (3)) or condition (4); only (4) is included, because (3) as printed is false ($A=\operatorname{diag}(1,10)$, $\gamma=1$) and Theorem 2 uses only (4). The conditional moments require $E|\xi_t|^2<\infty$; conditioning on $\mathcal F_{t-1}$ is written with $\xi_{t+1}$ given $\mathcal F_t$; the limsup-in-probability of Assumption 2.4 is unfolded as in the definition file; convergence of $E(\xi_t\xi_t^T\mid\mathcal F_{t-1})$ is entrywise. The limit law is the Gaussian measure on $\mathbb R^N$ with mean $0$ and covariance $V$, which is positive definite here.
-- source:
--   Polyak, Juditsky, Acceleration of stochastic approximation by averaging, SIAM J. Control Optim. 30 (1992), p. 839, Theorem 1(a), Eq. (2), (4), (5), Assumptions 2.1–2.4, 2.5(a)

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model
import Definitions.Def_PolyakJuditsky_Averaging_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology

namespace PolyakJuditsky.Averaging

/-- Theorem 1(a) (p. 839) under condition (4): for the linear algorithm (2),
`x_t = x_{t-1} - γ_t (A x_{t-1} - b + ξ_t)`, `x̄_t = (1/t) ∑_{i=0}^{t-1} x_i`, with `Re λ_i(A) > 0`
(Assumption 2.1), step sizes satisfying (4) (Assumption 2.2), and noise satisfying
Assumptions 2.3, 2.4, 2.5(a), `√t (x̄_t - x*) → N(0, A⁻¹ S (A⁻¹)ᵀ)` in distribution, where
`A x* = b`. -/
theorem linear_sa_asymptotic_normality {N : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (A : Matrix (Fin N) (Fin N) ℝ) (b x₀ xstar : EuclideanSpace ℝ (Fin N)) (γ : ℕ → ℝ)
    (ξ : ℕ → Ω → EuclideanSpace ℝ (Fin N)) (S : Matrix (Fin N) (Fin N) ℝ)
    (hA : EigenRePos A) (hγ : StepCondition4 γ) (hξ : LinearNoiseAssumptions P ℱ ξ S)
    (hxstar : matApply A xstar = b) :
    TendstoInDistribution
      (fun (t : ℕ) (ω : Ω) =>
        Real.sqrt t • (saAverage x₀ γ (fun x => matApply A x - b) ξ t ω - xstar))
      atTop id (fun _ => P) (multivariateGaussian 0 (A⁻¹ * S * (A⁻¹).transpose)) := by sorry

end PolyakJuditsky.Averaging
