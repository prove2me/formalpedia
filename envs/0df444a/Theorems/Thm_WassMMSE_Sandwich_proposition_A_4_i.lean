-- Prove2me | Theorems.Thm_WassMMSE_Sandwich_proposition_A_4_i
-- name    : WassMMSE.Sandwich.proposition_A_4_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:19:23.827346+00:00
-- url     : https://prove2.me/theorems/f23663ca-e4b3-4e00-a2c0-d13994da2143
-- title:
--   Proposition A.4 (i), p. 39 — max {⟨D,Σ⟩ : Σ ∈ 𝒮} is attained and equals inf_{γ≥0, γ>λ_max(D)} γ(ρ² + ⟨γ(γI−D)⁻¹ − I, Σ̂⟩)
-- statement:
--   Let $D\in\mathbb S^d$, $\widehat\Sigma\in\mathbb S^d_+$ and $\rho\ge0$, and consider problem (A.5)
--   $$\sup_{\Sigma\succeq0}\ \langle D,\Sigma\rangle\quad\text{s.t.}\quad \operatorname{Tr}\big[\Sigma+\widehat\Sigma-2(\widehat\Sigma^{1/2}\Sigma\widehat\Sigma^{1/2})^{1/2}\big]\le\rho^2.$$
--   Then (A.5) is solvable, that is, some feasible $\Sigma^\star$ maximizes $\langle D,\Sigma\rangle$ over the feasible set, and its maximum equals
--   $$\inf_{\gamma\ge0,\ \gamma>\lambda_{\max}(D)}\ \gamma\Big(\rho^2+\big\langle\gamma(\gamma I_d-D)^{-1}-I_d,\widehat\Sigma\big\rangle\Big).\tag{A.6}$$
--
--   The proposition reduces a linear optimization over a Gelbrich ball of covariance matrices to a one-dimensional problem; it is the step behind the worst-case covariance computations of the paper and the search directions of its Frank–Wolfe method.
--
--   **Formalization Note** The supremum of (A.5) and the infimum of (A.6) are compared in `EReal`. The page calls (A.6) a convex problem; that adjective is descriptive and not part of the statement. At $d=0$ the mission's convention $\lambda_{\max}=0$ makes (A.6) an infimum over $\gamma>0$ of $\gamma\rho^2$, which is $0$, the value of (A.5).
-- source:
--   Nguyen, Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, arXiv:1911.03539v2, p. 39, (A.5), Proposition A.4 (i), (A.6)

import Mathlib
import Definitions.Def_WassersteinDRO_Gelbrich_psdSqrt
import Definitions.Def_WassMMSE_Sandwich_Programs

open Matrix Topology WassersteinDRO.Gelbrich

namespace WassMMSE.Sandwich

/-- Proposition A.4 (i) (arXiv:1911.03539v2, p. 39): for `D ∈ 𝕊^d`, `Σ̂ ∈ 𝕊^d_+`, `ρ ≥ 0`, the
problem (A.5) `sup {⟨D, Σ⟩ : Σ ∈ 𝒮}` is solvable, and its maximum equals the infimum of (A.6)
`inf_{γ ≥ 0, γ > λ_max(D)} γ(ρ² + ⟨γ(γI_d − D)⁻¹ − I_d, Σ̂⟩)`. -/
theorem proposition_A_4_i {d : ℕ} (D Sh : Matrix (Fin d) (Fin d) ℝ) (hD : D.IsHermitian)
    (hSh : Sh.PosSemidef) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (∃ Ss ∈ covGelbrichSet ρ Sh, ∀ S ∈ covGelbrichSet ρ Sh, frob D S ≤ frob D Ss) ∧
    (⨆ (S : Matrix (Fin d) (Fin d) ℝ) (_ : S ∈ covGelbrichSet ρ Sh), (frob D S : EReal)) =
      ⨅ (γ : ℝ) (_ : 0 ≤ γ ∧ lamMax D < γ),
        ((γ * (ρ ^ 2 + frob (γ • (γ • (1 : Matrix (Fin d) (Fin d) ℝ) - D)⁻¹ - 1) Sh) : ℝ) :
          EReal) := by sorry

end WassMMSE.Sandwich
