-- Prove2me | Theorems.Thm_TwoEchelonCVRP_Config_lbw_lower_bound
-- name    : TwoEchelonCVRP.Config.lbw_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:23:05.797984+00:00
-- url     : https://prove2.me/theorems/1aa96cd7-5aa0-45e2-a16a-2807aa9a7972
-- title:
--   §5.1 — LBW(M) is a lower bound on z(F(M))
-- statement:
--   Let $\lambda\in\mathbb R^{N_C}$ be arbitrary, let $\mu_k\le0$ for every satellite $k$ and $\mu_0\le0$, and let $\beta$ satisfy the penalty system (12). For every set $M$ of first-level routes visiting at least one satellite,
--   $$\mathrm{LBW}(M)\le z(F(M)).$$
--
--   It is the bound used in condition (e) of Proposition 1 and in the order in which the exact method examines configurations.
--
--   **Formalization Note** The comparison is in `EReal`, so it is trivially true when $F(M)$ is infeasible ($z(F(M))=+\infty$). The paper takes the penalties producing LD1; any admissible ones are allowed here, and $M$ need not belong to $\mathcal P$.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Oper. Res. 61(2) (2013), p. 305, §5.1, the definition of LBW(M)

import Mathlib
import Definitions.Def_TwoEchelonCVRP_Config_Bounds

namespace TwoEchelonCVRP.Config

/-- §5.1, p. 305: for penalties `μ ≤ 0`, `μ_0 ≤ 0`, any `λ` and any `β` satisfying (12), and every
configuration `M` with `N_S(M)` nonempty, `LBW(M) ≤ z(F(M))`. -/
theorem lbw_lower_bound (I : Instance) (RS : RouteSystem I)
    (β : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ) (μ : Fin I.ns → ℝ) (μ0 : ℝ)
    (hμ : ∀ k, μ k ≤ 0) (hμ0 : μ0 ≤ 0) (hβ : SatisfiesPenalty RS β lam μ μ0)
    (M : Finset RS.FR) (hM : (NS RS M).Nonempty) :
    ((LBW RS β lam μ μ0 M hM : ℝ) : EReal) ≤ zFM RS M := by sorry

end TwoEchelonCVRP.Config
