-- Prove2me | Theorems.Thm_TwoEchelonCVRP_Config_proposition_1
-- name    : TwoEchelonCVRP.Config.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:23:14.540974+00:00
-- url     : https://prove2.me/theorems/4a06e03f-0822-4e1e-b863-19a8b47dd43a
-- title:
--   Proposition 1 (necessity of (b)–(e)) — every solution cheaper than z(UB) uses a configuration passing the pruning tests
-- statement:
--   Consider a 2E-CVRP instance with at least one satellite and at least one customer, route families $\mathcal M$ and $\mathcal R$, and formulation $F$. Let $z(\mathrm{UB})$ be a real number, $\lambda\in\mathbb R^{N_C}$ arbitrary, $\mu_k\le0$ for every satellite $k$, $\mu_0\le0$, and $\beta$ a solution of the penalty system (12). Let $(x,y,q)$ be a feasible solution of $F$ whose cost is less than $z(\mathrm{UB})$, and let $M=\{r\in\mathcal M: y_r=1\}$ be its configuration. Then $M\in\mathcal P$, $N_S(M)\neq\emptyset$, and
--   1. (b) $\displaystyle\sum_{r\in M}\min\Bigl\{Q_1,\sum_{k\in R_r}m_kQ_2\Bigr\}\ge q_{\mathrm{tot}}$;
--   2. (c) $\displaystyle\sum_{r\in M}\sum_{k\in R_r}m_k\ge\Bigl\lceil\frac{q_{\mathrm{tot}}}{Q_2}\Bigr\rceil$;
--   3. (d) $U(M)<z(\mathrm{UB})-\mathrm{LB}_R$;
--   4. (e) $U(M)<z(\mathrm{UB})-\mathrm{LBW}(M)$.
--
--   Hence a configuration violating one of (b)–(e) cannot be the configuration of an optimal solution when $z(\mathrm{UB})$ exceeds the optimal cost, and can be discarded when $\mathcal P$ is generated.
--
--   **Formalization Note** Only the necessity of the conditions is stated: the converse in the paper's "if and only if" fails (conditions (b)–(e) ignore the satellite capacities $B_k$). Condition (a), $|R_r\cap R_{r'}|\le1$, is left out: it holds for some optimal solution, not for every one. "An optimal solution" is replaced by "a feasible solution of cost $<z(\mathrm{UB})$", the property the paper's own justification of (d) and (e) uses; $z(\mathrm{UB})$ is any real number. The penalties are any admissible ones rather than those producing LD1. The ceiling in (c) is the natural-number ceiling of the rational $q_{\mathrm{tot}}/Q_2$. Condition (e) is stated together with the nonemptiness of $N_S(M)$ needed for its minimum.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Oper. Res. 61(2) (2013), p. 305, Proposition 1, conditions (b)–(e)

import Mathlib
import Definitions.Def_TwoEchelonCVRP_Config_Bounds

namespace TwoEchelonCVRP.Config

/-- Proposition 1, p. 305, necessity of conditions (b)–(e) (condition (a) omitted). Let `z(UB)` be
a real number, `μ ≤ 0`, `μ_0 ≤ 0`, `λ` arbitrary and `β` a solution of (12). Every feasible solution
of F of cost less than `z(UB)` uses a configuration `M` (its set of first-level routes) that lies in
`𝒫` and satisfies
(b) `∑_{r ∈ M} min{Q_1, ∑_{k ∈ R_r} m_k Q_2} ≥ q_tot`,
(c) `∑_{r ∈ M} ∑_{k ∈ R_r} m_k ≥ ⌈q_tot/Q_2⌉`,
(d) `U(M) < z(UB) − LB_R`,
(e) `U(M) < z(UB) − LBW(M)` (`N_S(M)` being nonempty). -/
theorem proposition_1 (I : Instance) (RS : RouteSystem I) (hns : 0 < I.ns) (hnc : 0 < I.nc)
    (β : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ) (μ : Fin I.ns → ℝ) (μ0 : ℝ)
    (hμ : ∀ k, μ k ≤ 0) (hμ0 : μ0 ≤ 0) (hβ : SatisfiesPenalty RS β lam μ μ0)
    (zUB : ℝ) (s : SolF RS) (hs : IsFeasibleF RS s) (hcost : costF RS s < zUB) :
    InP RS (conf s) ∧
    -- (b)
    I.qtot ≤ ∑ r ∈ conf s, min I.Q1 (∑ k ∈ RS.Rsat r, I.m k * I.Q2) ∧
    -- (c)
    ⌈(I.qtot : ℚ) / (I.Q2 : ℚ)⌉₊ ≤ ∑ r ∈ conf s, ∑ k ∈ RS.Rsat r, I.m k ∧
    -- (d)
    U RS (conf s) < zUB - LBR hns β lam μ μ0 ∧
    -- (e)
    ∃ hM : (NS RS (conf s)).Nonempty,
      U RS (conf s) < zUB - LBW RS β lam μ μ0 (conf s) hM := by sorry

end TwoEchelonCVRP.Config
