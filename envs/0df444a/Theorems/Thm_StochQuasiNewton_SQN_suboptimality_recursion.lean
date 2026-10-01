-- Prove2me | Theorems.Thm_StochQuasiNewton_SQN_suboptimality_recursion
-- name    : StochQuasiNewton.SQN.suboptimality_recursion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:39:13.230802+00:00
-- url     : https://prove2.me/theorems/0716fcee-de26-4394-98a8-da5d8ba797e1
-- title:
--   Eqs. (3.21)–(3.22) — recursion for the expected suboptimality
-- statement:
--   In the setting of Eq. (3.18) (a $C^2$ objective $F$ with $\lambda I\prec\nabla^2F\prec\Lambda I$, a Newton-like iteration with step lengths $\alpha^k>0$ and constants $0<\mu_1\le\mu_2$, $\gamma$), let $w^*$ minimize $F$ and put
--   $$\phi_k=E[F(w^k)-F(w^*)]\qquad(3.21).$$
--   Then for every $k\ge1$, $F(w^k)$ and $F(w^{k+1})$ are integrable and
--   $$\phi_{k+1}\le(1-2\alpha^k\mu_1\lambda)\,\phi_k+\frac\Lambda2(\alpha^k\mu_2)^2\gamma^2 .$$
--
--   This is the recursion from which the $O(1/k)$ rate of Theorem 3.2 is derived.
--
--   **Formalization Note** The step lengths are general ($\alpha^k>0$); the recursion does not use $\alpha^k=\beta/k$. The page's intermediate inequality (3.20) contains the typo $[F(w^k-F(w^*)]$ and is not restated.
-- source:
--   Byrd, Hansen, Nocedal, Singer, A Stochastic Quasi-Newton Method for Large-Scale Optimization, SIAM J. Optim. 26(2) (2016), p. 1017, Eqs. (3.21)–(3.22)

import Mathlib
import Definitions.Def_StochQuasiNewton_SQN_FiniteSum
import Definitions.Def_StochQuasiNewton_SQN_NewtonLike

open scoped RealInnerProductSpace
open MeasureTheory

namespace StochQuasiNewton.SQN

/-- Eqs. (3.21)–(3.22): in the setting of (3.18), with a minimizer `w*` of `F` and
`φ_k = E[F(w^k) − F(w*)]`, for every `k ≥ 1` the functions `F(w^k)`, `F(w^{k+1})` are integrable
and `φ_{k+1} ≤ (1 − 2 α^k μ₁ λ) φ_k + (Λ/2)(α^k μ₂)² γ²`. -/
theorem suboptimality_recursion {n : ℕ} {Ω Ξ : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace Ξ] (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ 2 F) (lam Lam : ℝ) (hlam : 0 < lam)
    (hLam : 0 < Lam)
    (hHess : ∀ w : EuclideanSpace ℝ (Fin n),
      StrictLoewnerBounds lam Lam (fderiv ℝ (gradient F) w))
    (wstar : EuclideanSpace ℝ (Fin n)) (hwstar : IsMinOn F Set.univ wstar)
    (G : EuclideanSpace ℝ (Fin n) → Ξ → EuclideanSpace ℝ (Fin n)) (γ : ℝ) (α : ℕ → ℝ)
    (hα : ∀ k, 1 ≤ k → 0 < α k) (μ₁ μ₂ : ℝ) (hμ₁ : 0 < μ₁) (hμ : μ₁ ≤ μ₂)
    (w1 : EuclideanSpace ℝ (Fin n)) (w : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (ξ : ℕ → Ω → Ξ)
    (H : ℕ → Ω → Matrix (Fin n) (Fin n) ℝ)
    (hrun : NewtonLikeIteration P ℱ F G γ α μ₁ μ₂ w1 w ξ H) (k : ℕ) (hk : 1 ≤ k) :
    Integrable (fun ω => F (w k ω)) P ∧ Integrable (fun ω => F (w (k + 1) ω)) P ∧
      ∫ ω, (F (w (k + 1) ω) - F wstar) ∂P ≤
        (1 - 2 * α k * μ₁ * lam) * ∫ ω, (F (w k ω) - F wstar) ∂P +
          Lam / 2 * (α k * μ₂) ^ 2 * γ ^ 2 := by sorry

end StochQuasiNewton.SQN
