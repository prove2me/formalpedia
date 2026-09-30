-- Prove2me | Theorems.Thm_StochQuasiNewton_SQN_newton_like_expected_suboptimality
-- name    : StochQuasiNewton.SQN.newton_like_expected_suboptimality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T22:40:06.428204+00:00
-- url     : https://prove2.me/theorems/9326a796-bd12-4fcb-a359-dbaeef41e7e0
-- title:
--   Theorem 3.2 — expected suboptimality Q(β)/k for the Newton-like iteration (corrected constant)
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R$ be $C^2$ with $\lambda I\prec\nabla^2F(w)\prec\Lambda I$ for all $w$ (3.4), $0<\lambda,\Lambda$, and let $w^*$ minimize $F$. Let $w^k,\xi^k,H_k$ be a Newton-like iteration (3.14) started at $w^1$, with $\mu_1I\prec H_k\prec\mu_2I$, $0<\mu_1\le\mu_2$ (3.15), conditionally unbiased stochastic gradients with conditional second moment at most $\gamma^2$, and step lengths
--   $$\alpha^k=\frac\beta k,\qquad\beta>\frac1{2\mu_1\lambda}.$$
--   Then for every $k\ge1$, $F(w^k)$ is integrable and
--   $$E[F(w^k)-F(w^*)]\le\frac{Q_c(\beta)}k,\qquad Q_c(\beta)=\max\Big\{\frac{\Lambda\mu_2^2\beta^2\gamma^2}{2(2\mu_1\lambda\beta-1)},\ \Lambda\mu_2^2\beta^2\gamma^2,\ F(w^1)-F(w^*)\Big\}.$$
--
--   This is the $O(1/k)$ convergence rate of stochastic Newton-like methods with uniformly bounded preconditioners, of which the SQN method is a special case.
--
--   **Formalization Note** *Corrected constant.* The paper states the bound with $Q(\beta)=\max\{\Lambda\mu_2^2\beta^2\gamma^2/(2(2\mu_1\lambda\beta-1)),\,F(w^1)-F(w^*)\}$ (3.17). That version is false: its induction multiplies the hypothesis by $1-2\beta\mu_1\lambda/k$, which is negative for $k<2\beta\mu_1\lambda$. Counterexample: $n=1$, $F(w)=w^2/2+1/2$ with stochastic gradients $w\mp1$ (each with probability $1/2$), $H_k=I$, $w^1=0$, $\beta=2$; then $F(w^2)-F(w^*)=2$ surely, while $Q(2)/2=5/3$ with $\gamma^2=5$ (strict hypotheses hold with $\lambda=\mu_1=1-\varepsilon$, $\Lambda=\mu_2=1+\varepsilon$). The middle entry of $Q_c$ repairs the early iterations; $Q_c=Q$ whenever $2\mu_1\lambda\beta\le3/2$. *Assumption 1(3).* The bound $\gamma^2$ on the second moment is imposed at the iterates, conditionally on the past, which is how the proof uses (3.5); the paper's "for all $w$" is unsatisfiable under (3.4). The hypothesis (3.3) on subsampled Hessians is not used by this theorem and is omitted.
-- source:
--   Byrd, Hansen, Nocedal, Singer, A Stochastic Quasi-Newton Method for Large-Scale Optimization, SIAM J. Optim. 26(2) (2016), pp. 1016–1017, Theorem 3.2, Eqs. (3.14)–(3.17)

import Mathlib
import Definitions.Def_StochQuasiNewton_SQN_FiniteSum
import Definitions.Def_StochQuasiNewton_SQN_NewtonLike

open scoped RealInnerProductSpace
open MeasureTheory

namespace StochQuasiNewton.SQN

/-- Theorem 3.2 (corrected constant): for the Newton-like iteration (3.14) on a `C²` objective
`F` with `λ I ≺ ∇²F(w) ≺ Λ I` (3.4) and minimizer `w*`, with `μ₁ I ≺ H_k ≺ μ₂ I`,
`0 < μ₁ ≤ μ₂` (3.15), step lengths `α^k = β/k` with `β > 1/(2 μ₁ λ)`, and the conditions of
`NewtonLikeIteration`, for every `k ≥ 1`, `F(w^k)` is integrable and
`E[F(w^k) − F(w*)] ≤ Q_c(β)/k`, where
`Q_c(β) = max { Λ μ₂² β² γ² / (2(2 μ₁ λ β − 1)), Λ μ₂² β² γ², F(w¹) − F(w*) }`. -/
theorem newton_like_expected_suboptimality {n : ℕ} {Ω Ξ : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace Ξ] (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ 2 F) (lam Lam : ℝ) (hlam : 0 < lam)
    (hLam : 0 < Lam)
    (hHess : ∀ w : EuclideanSpace ℝ (Fin n),
      StrictLoewnerBounds lam Lam (fderiv ℝ (gradient F) w))
    (wstar : EuclideanSpace ℝ (Fin n)) (hwstar : IsMinOn F Set.univ wstar)
    (G : EuclideanSpace ℝ (Fin n) → Ξ → EuclideanSpace ℝ (Fin n)) (γ μ₁ μ₂ β : ℝ)
    (hμ₁ : 0 < μ₁) (hμ : μ₁ ≤ μ₂) (hβ : 1 / (2 * μ₁ * lam) < β)
    (w1 : EuclideanSpace ℝ (Fin n)) (w : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (ξ : ℕ → Ω → Ξ)
    (H : ℕ → Ω → Matrix (Fin n) (Fin n) ℝ)
    (hrun : NewtonLikeIteration P ℱ F G γ (fun k => β / k) μ₁ μ₂ w1 w ξ H) :
    ∀ k : ℕ, 1 ≤ k →
      Integrable (fun ω => F (w k ω)) P ∧
        ∫ ω, (F (w k ω) - F wstar) ∂P ≤
          rateConstant Lam lam μ₁ μ₂ β γ (F w1 - F wstar) / k := by sorry

end StochQuasiNewton.SQN
