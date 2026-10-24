-- Prove2me | Theorems.Thm_ProdHedgeCVaR_Joint_proposition_4
-- name    : ProdHedgeCVaR.Joint.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:45:54.977433+00:00
-- url     : https://prove2.me/theorems/eb1358ca-bfda-4835-97b7-6bdb094864a6
-- title:
--   Proposition 4, p. 17 — s(m, Q) is jointly convex on {m ≥ 0, Q ≥ 0, m − pQ + C ≥ 0}, so (36) is a concave maximization problem
-- statement:
--   Throughout, $(\Omega,\mathcal F,\mathbb P)$ is a probability space carrying the terminal values of the model of §3: the asset-driven demand component $A_T\ge 0$, the asset noise $B_T\sim N(0,T)$, both measurable with respect to the hedger's information $\mathcal G$ (the paper's $\sigma(A_T,X_T)$), and $\xi\sim N(0,1)$ independent of $\mathcal G$. The demand is $D_T=A_T+\tilde\sigma\sqrt T\,\xi$, the production payoff $H_T(Q)=pQ-(p+c)(Q-D_T^+)^+$, and $Z_T=e^{-\eta B_T-\eta^2T/2}$ is the density of the martingale measure, $\mathsf E^M[Y]=\mathsf E[Z_TY]$. The parameters satisfy $p,c,\tilde\sigma,T,C>0$ and $\eta\ne0$. Let $s(m,Q)$ be the optimal shortfall of the static hedging problem (28), and let
--   $$\mathcal F=\{(m,Q): m\ge0,\ Q\ge0,\ m-pQ+C\ge0\}$$
--   be the feasible set of problem (36), on which $s$ is given by (34). Then $s$ is jointly convex on $\mathcal F$, and for every $\alpha\in(0,1)$ the objective
--   $$(m,Q)\mapsto m-\frac{1}{1-\alpha}\,s(m,Q)$$
--   of (36) is concave on the convex set $\mathcal F$.
--
--   Concavity makes the first-order conditions (45) and (53) sufficient for optimality in (36), which is how Theorem 2 identifies the optimum.
--
--   Differences from the source:
--
--   - reading: s(m, Q) of (22), 'completely characterized in (34)' (p. 16) → s(m, Q) is the optimal value of the static problem (28): the infimum of E[(m − H_T(Q) − V)⁺] over feasible terminal payoffs V; reason: (36) uses s through (34), which Theorem 1 derives from (28); that (22) and (28) have the same value is Proposition 2 (stochastic integration and martingale representation), not formalized
--   - encoding: (28): V_T a function of (A_T, X_T), V_T ≥ −C, E^M(V_T) ≤ 0 → V is G-measurable, V ≥ −C at every point, Z_T·V is integrable, and E[Z_T V] ≤ 0; reason: integrability is what makes E^M(V) defined; requiring V ≥ −C everywhere rather than a.s. gives the same infimum, since max(V, −C) is G-measurable and equals V a.s.
--   - generalization: the hedger's information is σ(A_T, X_T), with A_T adapted to the asset filtration F^X and B̃ a Brownian motion independent of B (§3, pp. 10–12) → any sub-σ-algebra G of the probability space such that A_T and B_T are G-measurable and ξ = B̃_T/√T is independent of G; reason: σ(A_T, X_T) = σ(A_T, B_T) (X_T is a strictly increasing function of B_T) satisfies these properties, so the paper's model is the instance G = σ(A_T, X_T); nothing else about G enters the statement
--   - encoding: the dynamic model: GBM asset (17), demand dD_t = dA_t + σ̃dB̃_t (18)–(19), density process (26) on [0, T] → the terminal values only: A_T ≥ 0, W = B_T with law N(0, T), ξ with law N(0, 1); Z_T = exp(−ηW − η²T/2), D_T = A_T + σ̃√T ξ; reason: every object in the statement is a function of (A_T, B_T, B̃_T); B̃_T has the law of √T ξ
--   - reading: p is the unit profit, c the net unit cost (p. 5), σ̃ > 0 (p. 10), T > 0 (p. 5), budget C > 0 (p. 12), η ≠ 0 (p. 13) → hypotheses p > 0, c > 0, σ̃ > 0, T > 0, C > 0, η ≠ 0 (Params.Valid); reason: the standing assumptions of §§2–3; c > 0 is needed: with c = 0 the second equation of (45) has no root, since its left-hand side stays below p(1 − α)
-- source:
--   Wang, Yao, Production Planning with Risk Hedging under a CVaR Objective, SSRN 3875464 (April 2020), p. 17, Proposition 4; proof §9.3, p. 35

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_ProdHedgeCVaR_Joint_Model

namespace ProdHedgeCVaR.Joint

open MeasureTheory ProbabilityTheory Filter Topology

/-- Proposition 4, p. 17: s(m, Q) is jointly convex on the domain of (34) and (36), and the
objective of (36) is concave there, so (36) is a concave maximization problem. -/
theorem proposition_4 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid) :
    ConvexOn ℝ {x : ℝ × ℝ | M.Feasible36 x} (fun x => M.s x.1 x.2) ∧
    ∀ α : ℝ, 0 < α → α < 1 → ConcaveOn ℝ {x : ℝ × ℝ | M.Feasible36 x} (M.obj α) := by sorry

end ProdHedgeCVaR.Joint
