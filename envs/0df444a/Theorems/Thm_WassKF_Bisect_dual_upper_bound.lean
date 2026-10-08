-- Prove2me | Theorems.Thm_WassKF_Bisect_dual_upper_bound
-- name    : WassKF.Bisect.dual_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:09:11.573166+00:00
-- url     : https://prove2.me/theorems/8d2a683b-e529-435f-b61e-e86776afd15e
-- title:
--   App. A.3, proof of Theorem 3.2, p. 13 — every γ with γI_d ≻ D gives the Lagrangian-dual bound γ(ρ² − Tr[Σ]) + γ²⟨(γI_d − D)⁻¹, Σ⟩ on (7b)
-- statement:
--   Let $\Sigma \in \mathbb{S}^d_{++}$, $D \in \mathbb{S}^d_+$, $\rho > 0$, $\underline{\sigma} = \lambda_{\min}(\Sigma)$, and let $\mathcal{F}$ be the feasible set of the direction-finding subproblem (7b),
--   $$
--   \mathcal{F} = \Big\{ L \succeq \underline{\sigma} I_d \;:\; \mathrm{Tr}\Big[L + \Sigma - 2\big(\Sigma^{1/2} L \Sigma^{1/2}\big)^{1/2}\Big] \le \rho^2 \Big\}.
--   $$
--   For every $\gamma \ge 0$ with $\gamma I_d \succ D$ and every $L' \in \mathcal{F}$,
--   $$
--   \langle L', D\rangle \le \gamma\big(\rho^2 - \mathrm{Tr}[\Sigma]\big) + \gamma^2\big\langle(\gamma I_d - D)^{-1}, \Sigma\big\rangle ,
--   $$
--   where $\langle A, B\rangle = \mathrm{Tr}[A^\top B]$. In words: the objective value of every $\gamma$ in the Lagrangian dual $\min_{\gamma:\gamma I_d \succ D} \gamma(\rho^2 - \mathrm{Tr}[\Sigma]) + \gamma^2\langle(\gamma I_d - D)^{-1},\Sigma\rangle$ of (7b) bounds the optimal value of (7b) from above (weak duality).
--
--   This is the certificate Algorithm 1 uses to bound the suboptimality of its output.
--
--   **Formalization Note** $\mathcal{F}$ is `WassersteinDRO.Shrinkage.sdpFeasibleSet ρ Σ σ`, with $\underline\sigma$ passed as $\sigma$ as in the other items. The page states the dual and its role as an upper bound; the formal statement is the weak-duality inequality, which is the content used.
-- source:
--   Shafieezadeh-Abadeh, Nguyen, Kuhn, Mohajerin Esfahani, Wasserstein Distributionally Robust Kalman Filtering, arXiv:1809.08830v3, p. 13, App. A.3, proof of Theorem 3.2 (Lagrangian dual display); p. 9, Lemma A.1

import Mathlib
import Definitions.Def_WassersteinDRO_Shrinkage_sdpFeasibleSet

open Matrix

namespace WassKF.Bisect

/-- App. A.3, proof of Theorem 3.2 (p. 13): the optimal value of (7b) is bounded above by the
objective value of every `γ` in the Lagrangian dual `min_{γ : γI_d ≻ D} γ(ρ² − Tr[Σ]) +
γ²⟨(γI_d − D)⁻¹, Σ⟩` (weak duality). `⟨A, B⟩ = Tr[AᵀB]`; the feasible set of (7b) is
`sdpFeasibleSet ρ Σ σ̲` with `σ̲ = λ_min(Σ)` passed as `σ`. -/
theorem dual_upper_bound {n m : ℕ} (Sigma D : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)
    (ρ σ : ℝ) (hρ : 0 < ρ) (hSigma : Sigma.PosDef) (hD : D.PosSemidef)
    (hσ : (Sigma - σ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)).PosSemidef)
    (hσ_eig : ∃ v : Fin n ⊕ Fin m → ℝ, v ≠ 0 ∧ Sigma *ᵥ v = σ • v)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ : (γ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D).PosDef)
    (L' : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)
    (hL' : L' ∈ WassersteinDRO.Shrinkage.sdpFeasibleSet ρ Sigma σ) :
    (L'ᵀ * D).trace ≤
      γ * (ρ ^ 2 - Sigma.trace) +
        γ ^ 2 * (((γ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D)⁻¹)ᵀ * Sigma).trace := by sorry

end WassKF.Bisect
