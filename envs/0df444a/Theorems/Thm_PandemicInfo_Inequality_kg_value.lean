-- Prove2me | Theorems.Thm_PandemicInfo_Inequality_kg_value
-- name    : PandemicInfo.Inequality.kg_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:34:11.255706+00:00
-- url     : https://prove2.me/theorems/be2c1db6-e6c0-4f68-b4f2-c4ca9ae7d890
-- title:
--   Proof of Theorem 1, p. 19 (PDF 20) — the optimal cost of (6) at the prior mean $\mu^\circ$ is $k_\lambda(\mu^\circ)$
-- statement:
--   Fix the model of §2 and a weight $\lambda\in[0,1]$. The minimum of the government's cost $C_\lambda(\Gamma,a)$ over all information policies $\Gamma$ with a finite message space and all Bayesian Nash equilibrium profiles $a$ is the lower convex envelope of $\tilde K_\lambda$ on $[\omega_\ell,\omega_h]$ evaluated at the prior mean:
--
--   $$\min_{\Gamma,\ a\in\mathcal B(\Gamma)}C_\lambda(\Gamma,a)=k_\lambda(\mu^\circ),\qquad \mu^\circ=\rho^\circ\omega_h+(1-\rho^\circ)\omega_\ell.$$
--
--   This is the Kamenica–Gentzkow (2011, Corollary 2) reduction applied to this model; Proposition 1 enters because the cost of any BNE profile at the posterior mean $\mu$ is $\tilde K_\lambda(\mu)$.
--
--   **Formalization Note** The value is stated as an attained minimum (`IsLeast`) of the set of attainable costs. Message spaces are finite types. The statement holds for every prior $\rho^\circ\in(0,1)$, which is the paper's "any prior mean". All statements assume the standing assumptions of §2 (`Params.Standing`).
-- source:
--   de Véricourt, Gurkan, Wang, Informing the Public about a Pandemic, ESMT Working Paper 20-03 (Dec. 15, 2020), p. 19 (PDF 20), proof of Theorem 1, 'Following Corollary 2 of Kamenica and Gentzkow (2011), …'

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_PandemicInfo_Inequality_Model
import Definitions.Def_PandemicInfo_Inequality_Reduced

namespace PandemicInfo.Inequality

/-- Proof of Theorem 1, p. 19 (Kamenica–Gentzkow, Corollary 2): the optimal value of (6) at the
prior mean `µ°` is attained at `k_λ(µ°)`, the minimum of `C_λ(Γ, a)` over finite-message
policies `Γ` and BNE profiles `a`. -/
theorem kg_value (P : Params) (hS : P.Standing) (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    IsLeast {v : ℝ | ∃ (M : Type) (_ : Fintype M) (π : Fin 2 → M → ℝ) (a : ℝ → ℝ → ℝ),
        IsPolicy π ∧ P.IsBNEProfile a ∧ v = P.govCost lam π a}
      (P.kEnv lam P.μ0) := by sorry

end PandemicInfo.Inequality
