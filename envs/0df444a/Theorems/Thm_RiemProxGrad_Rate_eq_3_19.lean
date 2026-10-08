-- Prove2me | Theorems.Thm_RiemProxGrad_Rate_eq_3_19
-- name    : RiemProxGrad.Rate.eq_3_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:47.182032+00:00
-- url     : https://prove2.me/theorems/d52e0faf-6dfb-4731-92ef-8d13a2a46878
-- title:
--   (3.19) — averaged bound $\frac1k\sum_{s=0}^{k-1}F(x_{s+1})-F(x_*)\le\frac{\tilde L}{2k}(\dots)+\frac{\tilde L\kappa_\Omega}{2\beta k}(F(x_0)-F(x_*))$
-- statement:
--   Work in the setting of Theorem 3.2: $\mathcal M$ is a finite-dimensional Riemannian manifold with retraction $R$, $F=f+g$, $0<\tilde L$, $L<\tilde L$, $\beta=(\tilde L-L)/2$, Assumptions 3.1, 3.3 (with the open set $\Omega\supseteq\Omega_{x_0}$) and 3.4 (with the constant $\kappa_\Omega$ and an inverse retraction $R^{-1}$ on $\Omega$) hold, $\{x_k\},\{\eta^*_{x_k}\}$ is a run of Algorithm 1 with $R_{x_k}^{-1}(x_{k+1})=\eta^*_{x_k}$ for every $k$, and $x_*$ is an accumulation point of $\{x_k\}$. Then for every $k\ge1$,
--   $$\frac1k\sum_{s=0}^{k-1}F(x_{s+1})-F(x_*)\le\frac{\tilde L}{2k}\left(\|R_{x_0}^{-1}(x_*)\|_{x_0}^2-\|R_{x_k}^{-1}(x_*)\|_{x_k}^2\right)+\frac{\tilde L\kappa_\Omega}{2\beta k}\bigl(F(x_0)-F(x_*)\bigr). \tag{3.19}$$
--
--   This is the average of (3.18) over the first $k$ steps. Since $F(x_k)$ is nonincreasing, it yields the rate (3.16) of Theorem 3.2.
--
--   **Formalization Note** The sentence before (3.19) on p. 12 says "summing (3.18) over $k$ from $0$ to $s-1$ and dividing the result by $s$"; the display sums over $s$ from $0$ to $k-1$ and divides by $k$, and the display is what is stated. The case $k=0$ is excluded because the paper divides by $k$.
-- source:
--   Huang, Wei, Riemannian proximal gradient methods, arXiv:1909.06065v4, p. 12, §3.2, proof of Theorem 3.2, (3.19)

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

/-- Display (3.19) in the proof of Theorem 3.2 (p. 12). Under Assumptions 3.1, 3.3 and 3.4, for a
run of Algorithm 1, an accumulation point `x*` of `{x_k}` and every `k ≥ 1`:
`(1/k) Σ_{s=0}^{k−1} F(x_{s+1}) − F(x*) ≤ (L̃/(2k))(‖R_{x_0}⁻¹(x*)‖² − ‖R_{x_k}⁻¹(x*)‖²)
  + (L̃ κ_Ω / (2βk))(F(x_0) − F(x*))`. -/
theorem eq_3_19
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
    (k : ℕ) (hk : 1 ≤ k) :
    (1 / (k : ℝ)) * ∑ s ∈ Finset.range k, objective f g (x (s + 1)) - objective f g xstar ≤
      Ltilde / (2 * k) * (‖Rinv (x 0) xstar‖ ^ 2 - ‖Rinv (x k) xstar‖ ^ 2) +
        Ltilde * κ / (2 * beta L Ltilde * k) * (objective f g (x 0) - objective f g xstar) := by sorry

end RiemProxGrad.Rate
