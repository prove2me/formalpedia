-- Prove2me | Theorems.Thm_TwoEchelonCVRP_Config_proposition_2
-- name    : TwoEchelonCVRP.Config.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:21:02.876901+00:00
-- url     : https://prove2.me/theorems/3b79d8eb-e754-413e-a630-0cf8257753f6
-- title:
--   Proposition 2 — a satellite supply bound θ that needs too many second-level vehicles makes F(M) infeasible
-- statement:
--   Let $M\in\mathcal P$ be a configuration and let $\theta(k)$, $k\in N_S(M)$, be real numbers such that every feasible solution of $F(M)$ supplies at least $\theta(k)$ to satellite $k$:
--   $$\theta(k)\le\sum_{r\in M_k}q_{kr}\qquad\text{for every feasible solution of }F(M)\text{ and every }k\in N_S(M).$$
--   If
--   $$\sum_{k\in N_S(M)}\Bigl\lceil\frac{\theta(k)}{Q_2}\Bigr\rceil>m^2\qquad\text{or}\qquad\Bigl\lceil\frac{\theta(k)}{Q_2}\Bigr\rceil>m_k\ \text{ for some }k\in N_S(M),$$
--   then $F(M)$ has no feasible solution, so $M$ can be removed from $\mathcal P$.
--
--   This is the second pruning test used to generate $\mathcal P$.
--
--   **Formalization Note** The ceilings are integer ceilings of real numbers. The paper writes "for some $k\in N_S$"; $\theta$ is only defined on $N_S(M)$, so the condition is read for $k\in N_S(M)$. The bound $\theta$ is a hypothesis; the paper's way of computing it, problem (27)–(32), is not part of this statement.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Oper. Res. 61(2) (2013), p. 305, Proposition 2

import Mathlib
import Definitions.Def_TwoEchelonCVRP_Config_Configuration

namespace TwoEchelonCVRP.Config

/-- Proposition 2, p. 305: let `M ∈ 𝒫` and let `θ(k)`, `k ∈ N_S(M)`, be a lower bound on the
quantity `∑_{r ∈ M_k} q_{kr}` supplied to satellite `k` in every feasible F(M) solution. If
`∑_{k ∈ N_S(M)} ⌈θ(k)/Q_2⌉ > m^2`, or `⌈θ(k)/Q_2⌉ > m_k` for some `k ∈ N_S(M)`, then F(M) has no
feasible solution. -/
theorem proposition_2 (I : Instance) (RS : RouteSystem I) (M : Finset RS.FR) (hMP : InP RS M)
    (θ : Fin I.ns → ℝ)
    (hθ : ∀ t : SolFM RS, IsFeasibleFM RS M t → ∀ k ∈ NS RS M, θ k ≤ ∑ r ∈ Mk RS M k, t.qd r k)
    (htest : (I.m2 : ℤ) < ∑ k ∈ NS RS M, ⌈θ k / (I.Q2 : ℝ)⌉ ∨
      ∃ k ∈ NS RS M, (I.m k : ℤ) < ⌈θ k / (I.Q2 : ℝ)⌉) :
    ∀ t : SolFM RS, ¬ IsFeasibleFM RS M t := by sorry

end TwoEchelonCVRP.Config
