-- Prove2me | Theorems.Thm_PandemicInfo_Inequality_Ktil_closed_form
-- name    : PandemicInfo.Inequality.Ktil_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:34:06.028802+00:00
-- url     : https://prove2.me/theorems/bc11ebaf-ad51-4578-9e03-81b0dc7d72b2
-- title:
--   (39), proof of Lemma 3, p. 22 (PDF 23) — closed form of $\tilde K_\lambda(\mu)$
-- statement:
--   For $\lambda\in[0,1]$ and every $\mu\in[\omega_\ell,\omega_h]$, the reduced cost $\tilde K_\lambda(\mu)=\lambda K_e(c^\star(\mu))+(1-\lambda)K_h(c^\star(\mu))$, defined by the expectations (9)–(10) over $c$ uniform on $\mathcal C$, equals
--
--   $$\tilde K_\lambda(\mu)=\frac{3\lambda-2}{2\gamma}\Big(\frac{\mu\kappa(\theta+\gamma/2)}{\gamma+\mu\kappa}\Big)^2+(1-\lambda)\Big(\frac{\mu\kappa(\theta+\gamma/2)}{\gamma+\mu\kappa}\Big)\frac{\theta+\gamma/2}{\gamma}-\frac{\lambda(\theta-\gamma/2)^2}{2\gamma},$$
--
--   where $\gamma=2\sigma\sqrt3$.
--
--   This closed form is what the curvature analysis of Lemma 3 differentiates.
--
--   **Formalization Note** The standing assumption $\omega_\ell\kappa\ge\inf\mathcal C$ is what places $c^\star(\mu)$ inside $\mathcal C$ for $\mu\ge\omega_\ell$; without it the formula fails. All statements assume the standing assumptions of §2 (`Params.Standing`).
-- source:
--   de Véricourt, Gurkan, Wang, Informing the Public about a Pandemic, ESMT Working Paper 20-03 (Dec. 15, 2020), p. 22 (PDF 23), proof of Lemma 3, (39)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_PandemicInfo_Inequality_Model
import Definitions.Def_PandemicInfo_Inequality_Reduced

namespace PandemicInfo.Inequality

/-- (39), proof of Lemma 3, p. 22: the closed form of `K̃_λ(µ)` on `[ω_ℓ, ω_h]`. -/
theorem Ktil_closed_form (P : Params) (hS : P.Standing) (lam : ℝ) (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1) (μ : ℝ) (hμ : μ ∈ Set.Icc P.ωl P.ωh) :
    P.Ktil lam μ =
      (3 * lam - 2) / (2 * P.γ) * (μ * P.κ * (P.θ + P.γ / 2) / (P.γ + μ * P.κ)) ^ 2 +
        (1 - lam) * (μ * P.κ * (P.θ + P.γ / 2) / (P.γ + μ * P.κ)) * (P.θ + P.γ / 2) / P.γ -
        lam * (P.θ - P.γ / 2) ^ 2 / (2 * P.γ) := by sorry

end PandemicInfo.Inequality
