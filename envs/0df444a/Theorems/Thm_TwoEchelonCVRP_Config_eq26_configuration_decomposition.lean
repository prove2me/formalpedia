-- Prove2me | Theorems.Thm_TwoEchelonCVRP_Config_eq26_configuration_decomposition
-- name    : TwoEchelonCVRP.Config.eq26_configuration_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:21:04.574345+00:00
-- url     : https://prove2.me/theorems/86563507-2ab1-4ca0-8133-63167defc08a
-- title:
--   Eq. (26) — z(F) = min over configurations M ∈ 𝒫 of U(M) + z(F(M))
-- statement:
--   Consider a 2E-CVRP instance with route families $\mathcal M$ and $\mathcal R$, its formulation $F$ with optimal value $z(F)$, the set $\mathcal P$ of configurations, and for each $M\in\mathcal P$ the problem $F(M)$ with optimal value $z(F(M))$ ($+\infty$ when infeasible). Then
--   $$z(F)=\min_{M\in\mathcal P}\bigl\{U(M)+z(F(M))\bigr\},$$
--   where $U(M)=\sum_{r\in M}g_r$ is the first-level cost of $M$ (and both sides are $+\infty$ when $F$ is infeasible).
--
--   This is the reformulation on which the exact method rests: the 2E-CVRP splits into a choice of a configuration of first-level routes and a second-level problem $F(M)$ for that configuration.
--
--   **Formalization Note** Optimal values are infima in `EReal`; the minimum over $\mathcal P$ is an infimum over the finite set `configs`. In $F(M)$ the deliveries are real, in $F$ they are integers, exactly as printed. The equality uses that demands are positive integers.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Oper. Res. 61(2) (2013), p. 305, §5, Eq. (26)

import Mathlib
import Definitions.Def_TwoEchelonCVRP_Config_Configuration

namespace TwoEchelonCVRP.Config

/-- Eq. (26), §5, p. 305: `z(F) = min_{M ∈ 𝒫} {U(M) + z(F(M))}`, with optimal values in `EReal`
(`⊤` for an infeasible problem). -/
theorem eq26_configuration_decomposition (I : Instance) (RS : RouteSystem I) :
    zF RS = ⨅ M ∈ configs RS, ((U RS M : ℝ) : EReal) + zFM RS M := by sorry

end TwoEchelonCVRP.Config
