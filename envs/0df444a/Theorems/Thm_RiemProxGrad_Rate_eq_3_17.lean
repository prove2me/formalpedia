-- Prove2me | Theorems.Thm_RiemProxGrad_Rate_eq_3_17
-- name    : RiemProxGrad.Rate.eq_3_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:56.928037+00:00
-- url     : https://prove2.me/theorems/74f45205-c3f0-427b-9125-6f7d749e8e88
-- title:
--   (3.17) — $F(x_{k+1})-F(x_*)\le(\tilde L/2)(\|R_{x_k}^{-1}(x_*)\|^2-\|R_{x_{k+1}}^{-1}(x_*)\|^2)+(\tilde L/2)\kappa_\Omega\|\eta^*_{x_k}\|^2$
-- statement:
--   Work in the setting of Theorem 3.2: $\mathcal M$ is a finite-dimensional Riemannian manifold with retraction $R$, $F=f+g$, $0<\tilde L$, $L<\tilde L$, Assumptions 3.1, 3.3 (with the open set $\Omega\supseteq\Omega_{x_0}$) and 3.4 (with the constant $\kappa_\Omega$ and an inverse retraction $R^{-1}$ on $\Omega$) hold, $\{x_k\},\{\eta^*_{x_k}\}$ is a run of Algorithm 1 with $R_{x_k}^{-1}(x_{k+1})=\eta^*_{x_k}$ for every $k$, and $x_*$ is an accumulation point of $\{x_k\}$. Then for every $k\ge0$,
--   $$\begin{aligned}F(x_{k+1})-F(x_*)&\le\frac{\tilde L}{2}\left(\|R_{x_k}^{-1}(x_*)\|_{x_k}^2-\|R_{x_k}^{-1}(x_*)-\eta^*_{x_k}\|_{x_k}^2\right)\\&\le\frac{\tilde L}{2}\left(\|R_{x_k}^{-1}(x_*)\|_{x_k}^2-\|R_{x_{k+1}}^{-1}(x_*)\|_{x_{k+1}}^2\right)+\frac{\tilde L}{2}\kappa_\Omega\|\eta^*_{x_k}\|_{x_k}^2.\end{aligned}\tag{3.17}$$
--
--   The first inequality is Lemma 3.4 with $x=x_k$ and $y=x_*$; the second is Assumption 3.4 with $x=x_k$, $y=x_{k+1}$, $z=x_*$. Together they give a one-step estimate whose first term telescopes.
--
--   **Formalization Note** Both inequalities of the chain are stated, as a conjunction. The norms live in different tangent spaces: $T_{x_k}\mathcal M$ and $T_{x_{k+1}}\mathcal M$. The hypothesis $R_{x_k}^{-1}(x_{k+1})=\eta^*_{x_k}$ makes explicit the identification the proof uses when it applies (3.12) with $y=x_{k+1}$.
-- source:
--   Huang, Wei, Riemannian proximal gradient methods, arXiv:1909.06065v4, p. 12, §3.2, proof of Theorem 3.2, (3.17)

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

/-- Display (3.17) in the proof of Theorem 3.2 (p. 12). Under Assumptions 3.1, 3.3 and 3.4, for a
run of Algorithm 1, an accumulation point `x*` of `{x_k}` and every `k`:
`F(x_{k+1}) − F(x*) ≤ (L̃/2)(‖R_{x_k}⁻¹(x*)‖² − ‖R_{x_k}⁻¹(x*) − η*_{x_k}‖²)
  ≤ (L̃/2)(‖R_{x_k}⁻¹(x*)‖² − ‖R_{x_{k+1}}⁻¹(x*)‖²) + (L̃/2) κ_Ω ‖η*_{x_k}‖²`. -/
theorem eq_3_17
    (f g : M → ℝ) (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M)
    (Rinv : (x : M) → M → TangentSpace 𝓘(ℝ, E) x) (L Ltilde κ : ℝ) (Ω : Set M)
    (x : ℕ → M) (η : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k))
    (hP : StandingAssumptions f g grad R) (hLt : 0 < Ltilde) (hL : L < Ltilde)
    (h31 : Assumption31 (objective f g) (x 0))
    (h33 : Assumption33 f g grad R L (x 0) Ω)
    (hinv : IsInverseRetractionOn R Rinv Ω) (h34 : Assumption34 Rinv Ω κ)
    (hrun : IsRPGRun grad g R Ltilde x η)
    (hsel : ∀ k, Rinv (x k) (x (k + 1)) = η k)
    (xstar : M) (hxstar : MapClusterPt xstar atTop x)
    (k : ℕ) :
    objective f g (x (k + 1)) - objective f g xstar ≤
        Ltilde / 2 * (‖Rinv (x k) xstar‖ ^ 2 - ‖Rinv (x k) xstar - η k‖ ^ 2) ∧
      Ltilde / 2 * (‖Rinv (x k) xstar‖ ^ 2 - ‖Rinv (x k) xstar - η k‖ ^ 2) ≤
        Ltilde / 2 * (‖Rinv (x k) xstar‖ ^ 2 - ‖Rinv (x (k + 1)) xstar‖ ^ 2) +
          Ltilde / 2 * κ * ‖η k‖ ^ 2 := by sorry

end RiemProxGrad.Rate
