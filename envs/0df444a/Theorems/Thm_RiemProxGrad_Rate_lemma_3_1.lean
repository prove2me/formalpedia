-- Prove2me | Theorems.Thm_RiemProxGrad_Rate_lemma_3_1
-- name    : RiemProxGrad.Rate.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:24:44.489548+00:00
-- url     : https://prove2.me/theorems/2e1278f3-e6e8-4181-b0cc-a31027a6872a
-- title:
--   Lemma 3.1 — RPG descent: $F(x_k)-F(x_{k+1})\ge\beta\|\eta^*_{x_k}\|^2$, $\beta=(\tilde L-L)/2$
-- statement:
--   Let $\mathcal M$ be a finite-dimensional Riemannian manifold with retraction $R$, and let $F=f+g$ with $f$ differentiable (gradient $\operatorname{grad} f$) and $g$ continuous with locally Lipschitz pull-backs $g\circ R_x$. Let $0<\tilde L$ and $L<\tilde L$, and suppose $f$ is $L$-retraction-smooth with respect to $R$ in the sublevel set $\Omega_{x_0}=\{x\mid F(x)\le F(x_0)\}$ (Assumption 3.2). Then every run $\{x_k\}$, $\{\eta^*_{x_k}\}$ of Algorithm 1 satisfies, for every $k\ge0$,
--   $$F(x_k)-F(x_{k+1})\ge\beta\,\|\eta^*_{x_k}\|_{x_k}^2,\qquad \beta=\frac{\tilde L-L}{2}. \tag{3.5}$$
--
--   The lemma says that the Riemannian proximal gradient method is a descent method without any convexity of $g$. In the rate analysis it keeps the iterates in $\Omega_{x_0}$ and turns the term $\|\eta^*_{x_k}\|^2$ of (3.17) into a decrease of $F$.
--
--   **Formalization Note** Assumption 3.2 is used in the form where (3.2) holds for every tangent vector $\eta$ at points of $\Omega_{x_0}$ (Definition 3.1 asks it only for $\eta$ with $R_x(\eta)\in\Omega_{x_0}$; under that literal reading the lemma fails). $\tilde L>0$ is the algorithm's input condition.
-- source:
--   Huang, Wei, Riemannian proximal gradient methods, arXiv:1909.06065v4, p. 7, Lemma 3.1, (3.5)

import Mathlib
import Definitions.Def_RiemOpt_BFGS_Setting
import Definitions.Def_RiemOpt_FR_Setting
import Definitions.Def_RiemProxGrad_Global_Setting
import Definitions.Def_RiemProxGrad_Rate_Setting

open Bundle Manifold Filter
open scoped ContDiff

namespace RiemProxGrad.Rate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]

/-- Lemma 3.1 (p. 7). Under Assumption 3.2, every run of Algorithm 1 is a descent method:
`F(x_k) − F(x_{k+1}) ≥ β ‖η*_{x_k}‖²_{x_k}` with `β = (L̃ − L)/2` (3.5). -/
theorem lemma_3_1
    (f g : M → ℝ) (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M)
    (L Ltilde : ℝ) (x : ℕ → M) (η : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k))
    (hP : StandingAssumptions f g grad R) (hLt : 0 < Ltilde) (hL : L < Ltilde)
    (h32 : Assumption32 f g grad R L (x 0))
    (hrun : IsRPGRun grad g R Ltilde x η) (k : ℕ) :
    objective f g (x k) - objective f g (x (k + 1)) ≥ beta L Ltilde * ‖η k‖ ^ 2 := by sorry

end RiemProxGrad.Rate
