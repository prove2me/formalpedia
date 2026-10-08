-- Prove2me | Theorems.Thm_RiemProxGrad_Rate_eq_3_18
-- name    : RiemProxGrad.Rate.eq_3_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:50.461136+00:00
-- url     : https://prove2.me/theorems/0632877d-b118-4665-9caf-f229f98b0d59
-- title:
--   (3.18) — one-step bound $F(x_{k+1})-F(x_*)\le\dots+(\tilde L\kappa_\Omega/(2\beta))(F(x_k)-F(x_{k+1}))$
-- statement:
--   Work in the setting of Theorem 3.2: $\mathcal M$ is a finite-dimensional Riemannian manifold with retraction $R$, $F=f+g$, $0<\tilde L$, $L<\tilde L$, $\beta=(\tilde L-L)/2$, Assumptions 3.1, 3.3 (with the open set $\Omega\supseteq\Omega_{x_0}$) and 3.4 (with the constant $\kappa_\Omega$ and an inverse retraction $R^{-1}$ on $\Omega$) hold, $\{x_k\},\{\eta^*_{x_k}\}$ is a run of Algorithm 1 with $R_{x_k}^{-1}(x_{k+1})=\eta^*_{x_k}$ for every $k$, and $x_*$ is an accumulation point of $\{x_k\}$. Then for every $k\ge0$,
--   $$F(x_{k+1})-F(x_*)\le\frac{\tilde L}{2}\left(\|R_{x_k}^{-1}(x_*)\|_{x_k}^2-\|R_{x_{k+1}}^{-1}(x_*)\|_{x_{k+1}}^2\right)+\frac{\tilde L\kappa_\Omega}{2\beta}\bigl(F(x_k)-F(x_{k+1})\bigr). \tag{3.18}$$
--
--   The estimate combines the descent inequality (3.5) with (3.17); both terms on the right telescope when summed over $k$.
-- source:
--   Huang, Wei, Riemannian proximal gradient methods, arXiv:1909.06065v4, p. 12, §3.2, proof of Theorem 3.2, (3.18)

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

/-- Display (3.18) in the proof of Theorem 3.2 (p. 12). Under Assumptions 3.1, 3.3 and 3.4, for a
run of Algorithm 1, an accumulation point `x*` of `{x_k}` and every `k`:
`F(x_{k+1}) − F(x*) ≤ (L̃/2)(‖R_{x_k}⁻¹(x*)‖² − ‖R_{x_{k+1}}⁻¹(x*)‖²)
  + (L̃ κ_Ω / (2β))(F(x_k) − F(x_{k+1}))`, `β = (L̃ − L)/2`. -/
theorem eq_3_18
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
      Ltilde / 2 * (‖Rinv (x k) xstar‖ ^ 2 - ‖Rinv (x (k + 1)) xstar‖ ^ 2) +
        Ltilde * κ / (2 * beta L Ltilde) * (objective f g (x k) - objective f g (x (k + 1))) := by sorry

end RiemProxGrad.Rate
