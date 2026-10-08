-- Prove2me | Theorems.Thm_WassKF_Bisect_lemma_A_3
-- name    : WassKF.Bisect.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:09:30.979919+00:00
-- url     : https://prove2.me/theorems/1f459040-8093-41c7-acb6-afba2a87efec
-- title:
--   Lemma A.3 (Bisection interval), p. 13 — the root of h lies in [λ₁(1 + √(v₁ᵀΣv₁)/ρ), λ₁(1 + √Tr[Σ]/ρ)]
-- statement:
--   Let $\Sigma \in \mathbb{S}^d_{++}$, let $D \in \mathbb{S}^d_+$ with $D \neq 0$, and let $\rho > 0$. Let $\lambda_1$ be the largest eigenvalue of $D$ and $v_1$ a corresponding eigenvector with $\|v_1\| = 1$. If $\gamma^\star$ satisfies $\gamma^\star I_d \succ D$ and solves
--   $$
--   h(\gamma^\star) = \rho^2 - \big\langle \Sigma, \big(I_d - \gamma^\star(\gamma^\star I_d - D)^{-1}\big)^2\big\rangle = 0,
--   $$
--   then $\gamma_{\min} \le \gamma^\star \le \gamma_{\max}$, where
--   $$
--   \gamma_{\min} = \lambda_1\Big(1 + \sqrt{v_1^\top \Sigma v_1}/\rho\Big),\qquad \gamma_{\max} = \lambda_1\Big(1 + \sqrt{\mathrm{Tr}[\Sigma]}/\rho\Big).
--   $$
--   These are the initial bounds $LB$ and $UB$ of Algorithm 1.
--
--   **Formalization Note** The page says only that $v_1$ is "a corresponding eigenvector"; the normalisation $v_1^\top v_1 = 1$ is added, because $\gamma_{\min}$ scales with $\|v_1\|$ and the lemma is false for a rescaled eigenvector. "The largest eigenvalue" is encoded as $\lambda_1 I_d - D \succeq 0$ together with $Dv_1 = \lambda_1 v_1$. The lemma is stated for every nonzero $D \succeq 0$ (the class of Lemmas A.1–A.2), which contains $D = \nabla f(S)$; the page's "the solution" is read as "every solution with $\gamma^\star I_d \succ D$".
-- source:
--   Shafieezadeh-Abadeh, Nguyen, Kuhn, Mohajerin Esfahani, Wasserstein Distributionally Robust Kalman Filtering, arXiv:1809.08830v3, p. 13, Lemma A.3, (A.7)

import Mathlib
import Definitions.Def_WassKF_Bisect_hFun

open Matrix

namespace WassKF.Bisect

/-- Lemma A.3 (Bisection interval), p. 13: for `ρ > 0`, every solution `γ⋆` with `γ⋆I_d ≻ D` of
`h(γ⋆) = 0` lies in `[γ_min, γ_max]`, `γ_min = λ₁(1 + √(v₁ᵀΣv₁)/ρ)`, `γ_max = λ₁(1 + √Tr[Σ]/ρ)`
(A.7), where `λ₁` is the largest eigenvalue of `D` (`λ₁I − D ⪰ 0` and `Dv₁ = λ₁v₁`) and `v₁` is a
corresponding eigenvector, normalised to `v₁ᵀv₁ = 1` (added: the page says only "an eigenvector").
`D` is any nonzero positive semidefinite matrix, as in Lemmas A.1–A.2. -/
theorem lemma_A_3 {n m : ℕ} (Sigma D : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)
    (ρ : ℝ) (hρ : 0 < ρ) (hSigma : Sigma.PosDef) (hD : D.PosSemidef) (hD0 : D ≠ 0)
    (lam1 : ℝ) (v₁ : Fin n ⊕ Fin m → ℝ)
    (hlam : (lam1 • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D).PosSemidef)
    (hv : D *ᵥ v₁ = lam1 • v₁) (hv1 : v₁ ⬝ᵥ v₁ = 1)
    (γstar : ℝ)
    (hγstar : (γstar • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D).PosDef)
    (hroot : hFun Sigma D ρ γstar = 0) :
    lam1 * (1 + Real.sqrt (v₁ ⬝ᵥ (Sigma *ᵥ v₁)) / ρ) ≤ γstar ∧
      γstar ≤ lam1 * (1 + Real.sqrt Sigma.trace / ρ) := by sorry

end WassKF.Bisect
