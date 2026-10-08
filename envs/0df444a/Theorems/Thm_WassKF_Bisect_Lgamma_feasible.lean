-- Prove2me | Theorems.Thm_WassKF_Bisect_Lgamma_feasible
-- name    : WassKF.Bisect.Lgamma_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:10:44.314005+00:00
-- url     : https://prove2.me/theorems/c3540e4a-aa94-413c-88d1-23aff35ca587
-- title:
--   App. A.3, proof of Theorem 3.2, p. 13 — L(γ) is feasible in (7b) whenever γI_d ≻ D and h(γ) > 0
-- statement:
--   Let $\Sigma \in \mathbb{S}^d_{++}$, let $D \in \mathbb{S}^d_+$, let $\rho > 0$, and let $\underline{\sigma} = \lambda_{\min}(\Sigma)$. The direction-finding subproblem (7b) maximizes $\langle L, D\rangle$ over the feasible set
--   $$
--   \mathcal{F} = \Big\{ L \succeq \underline{\sigma} I_d \;:\; \mathrm{Tr}\Big[L + \Sigma - 2\big(\Sigma^{1/2} L \Sigma^{1/2}\big)^{1/2}\Big] \le \rho^2 \Big\}.
--   $$
--   If $\gamma I_d \succ D$ and $h(\gamma) > 0$, where $h(\gamma) = \rho^2 - \langle \Sigma, (I_d - \gamma(\gamma I_d - D)^{-1})^2\rangle$, then
--   $$
--   L(\gamma) = \gamma^2(\gamma I_d - D)^{-1}\Sigma(\gamma I_d - D)^{-1} \in \mathcal{F}.
--   $$
--   Both parts of feasibility are asserted: the transport-cost constraint and the eigenvalue bound $L(\gamma) \succeq \underline{\sigma} I_d$.
--
--   This is the step of the proof of Theorem 3.2 that makes every matrix the bisection can output feasible.
--
--   **Formalization Note** $\mathcal{F}$ is the published set `WassersteinDRO.Shrinkage.sdpFeasibleSet ρ Σ σ`, whose additional conjuncts ($L \succeq 0$ and its diagonal blocks $\succeq 0$) follow from $L \succeq \underline\sigma I_d$. $\underline{\sigma}$ is passed as a real $\sigma$ with $\Sigma - \sigma I_d \succeq 0$ and an eigenvector of $\Sigma$ for $\sigma$, which pins $\sigma = \lambda_{\min}(\Sigma)$.
-- source:
--   Shafieezadeh-Abadeh, Nguyen, Kuhn, Mohajerin Esfahani, Wasserstein Distributionally Robust Kalman Filtering, arXiv:1809.08830v3, p. 13, App. A.3, proof of Theorem 3.2 (first sentence); p. 12, proof of Lemma A.2 (eigenvalue estimate)

import Mathlib
import Definitions.Def_WassersteinDRO_Shrinkage_sdpFeasibleSet
import Definitions.Def_WassKF_Bisect_hFun
import Definitions.Def_WassKF_Bisect_Lgamma

open Matrix

namespace WassKF.Bisect

/-- App. A.3, proof of Theorem 3.2 (p. 13): `L(γ) = γ²(γI_d − D)⁻¹Σ(γI_d − D)⁻¹` is feasible in
(7b) for every `γ` with `γI_d ≻ D` and `h(γ) > 0`. The feasible set of (7b) is
`{L ⪰ σ̲I_d : Tr[L + Σ − 2(Σ^½ L Σ^½)^½] ≤ ρ²}` (`sdpFeasibleSet ρ Σ σ̲`), where `σ̲ = λ_min(Σ)` is
passed as `σ` with `Σ − σI ⪰ 0` and an eigenvector of `Σ` for `σ`. -/
theorem Lgamma_feasible {n m : ℕ} (Sigma D : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)
    (ρ σ γ : ℝ) (hρ : 0 < ρ) (hSigma : Sigma.PosDef) (hD : D.PosSemidef)
    (hσ : (Sigma - σ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)).PosSemidef)
    (hσ_eig : ∃ v : Fin n ⊕ Fin m → ℝ, v ≠ 0 ∧ Sigma *ᵥ v = σ • v)
    (hγ : (γ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D).PosDef)
    (hh : 0 < hFun Sigma D ρ γ) :
    Lgamma Sigma D γ ∈ WassersteinDRO.Shrinkage.sdpFeasibleSet ρ Sigma σ := by sorry

end WassKF.Bisect
