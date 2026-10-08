-- Prove2me | Theorems.Thm_WassKF_Bisect_suboptimality_bound
-- name    : WassKF.Bisect.suboptimality_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:12:16.875986+00:00
-- url     : https://prove2.me/theorems/015a6eff-5f33-4472-9a1c-288ce169f285
-- title:
--   App. A.3, proof of Theorem 3.2, p. 13 — ⟨L(γ⋆) − L(γ), D⟩ ≤ γ(ρ² − Tr[Σ]) + γ²⟨(γI_d − D)⁻¹, Σ⟩ − ⟨L(γ), D⟩
-- statement:
--   Let $\Sigma \in \mathbb{S}^d_{++}$, $D \in \mathbb{S}^d_+$ and $\rho > 0$, and write $h(\gamma) = \rho^2 - \langle\Sigma, (I_d - \gamma(\gamma I_d - D)^{-1})^2\rangle$ and $L(\gamma) = \gamma^2(\gamma I_d - D)^{-1}\Sigma(\gamma I_d - D)^{-1}$. Let $\gamma^\star$ satisfy $\gamma^\star I_d \succ D$ and $h(\gamma^\star) = 0$. Then for every $\gamma \ge 0$ with $\gamma I_d \succ D$,
--   $$
--   \big\langle L(\gamma^\star) - L(\gamma), D\big\rangle \le \gamma\big(\rho^2 - \mathrm{Tr}[\Sigma]\big) + \gamma^2\big\langle (\gamma I_d - D)^{-1}, \Sigma\big\rangle - \big\langle L(\gamma), D\big\rangle ,
--   $$
--   with $\langle A,B\rangle = \mathrm{Tr}[A^\top B]$.
--
--   Since $L(\gamma^\star)$ is optimal in (7b), the left side is the suboptimality of $L(\gamma)$, and the right side is exactly the quantity $\Delta$ that Algorithm 1 tests against the tolerance $\varepsilon$.
-- source:
--   Shafieezadeh-Abadeh, Nguyen, Kuhn, Mohajerin Esfahani, Wasserstein Distributionally Robust Kalman Filtering, arXiv:1809.08830v3, p. 13, App. A.3, proof of Theorem 3.2 (suboptimality display)

import Mathlib
import Definitions.Def_WassKF_Bisect_hFun
import Definitions.Def_WassKF_Bisect_Lgamma

open Matrix

namespace WassKF.Bisect

/-- App. A.3, proof of Theorem 3.2 (p. 13), suboptimality display: if `γ⋆I_d ≻ D` and
`h(γ⋆) = 0`, then for every `γ ≥ 0` with `γI_d ≻ D`,
`⟨L(γ⋆) − L(γ), D⟩ ≤ γ(ρ² − Tr[Σ]) + γ²⟨(γI_d − D)⁻¹, Σ⟩ − ⟨L(γ), D⟩`, where `⟨A, B⟩ = Tr[AᵀB]`
and `L(γ) = γ²(γI_d − D)⁻¹Σ(γI_d − D)⁻¹`. -/
theorem suboptimality_bound {n m : ℕ} (Sigma D : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)
    (ρ : ℝ) (hρ : 0 < ρ) (hSigma : Sigma.PosDef) (hD : D.PosSemidef)
    (γstar : ℝ)
    (hγstar : (γstar • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D).PosDef)
    (hroot : hFun Sigma D ρ γstar = 0)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ : (γ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D).PosDef) :
    ((Lgamma Sigma D γstar - Lgamma Sigma D γ)ᵀ * D).trace ≤
      γ * (ρ ^ 2 - Sigma.trace) +
        γ ^ 2 * (((γ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D)⁻¹)ᵀ * Sigma).trace -
        ((Lgamma Sigma D γ)ᵀ * D).trace := by sorry

end WassKF.Bisect
