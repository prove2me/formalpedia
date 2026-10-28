-- Prove2me | Theorems.Thm_ProdHedgeCVaR_Joint_eq_49
-- name    : ProdHedgeCVaR.Joint.eq_49
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:45:57.575985+00:00
-- url     : https://prove2.me/theorems/58f0b5c0-e5d5-4ba2-87d5-3994fccaddd6
-- title:
--   (49), p. 19 — 1 − α = E[1 − (1 − λ°Z_T)⁺] = E(1 ∧ λ°Z_T) ≤ λ°E(Z_T) = λ°
-- statement:
--   Throughout, $(\Omega,\mathcal F,\mathbb P)$ is a probability space carrying the terminal values of the model of §3: the asset-driven demand component $A_T\ge 0$, the asset noise $B_T\sim N(0,T)$, both measurable with respect to the hedger's information $\mathcal G$ (the paper's $\sigma(A_T,X_T)$), and $\xi\sim N(0,1)$ independent of $\mathcal G$. The demand is $D_T=A_T+\tilde\sigma\sqrt T\,\xi$, the production payoff $H_T(Q)=pQ-(p+c)(Q-D_T^+)^+$, and $Z_T=e^{-\eta B_T-\eta^2T/2}$ is the density of the martingale measure, $\mathsf E^M[Y]=\mathsf E[Z_TY]$. The parameters satisfy $p,c,\tilde\sigma,T,C>0$ and $\eta\ne0$. Let $\alpha\in(0,1)$ and let $\lambda^\circ$ solve the first equation of (45), $\mathsf E[(1-\lambda^\circ Z_T)^+]=\alpha$. Then
--   $$1-\alpha=\mathsf E\big[1-(1-\lambda^\circ Z_T)^+\big]=\mathsf E(1\wedge\lambda^\circ Z_T)\le\lambda^\circ\,\mathsf E(Z_T)=\lambda^\circ.\qquad(49)$$
--
--   In particular $\lambda^\circ\ge1-\alpha>0$; this is the last inequality of (47).
--
--   Differences from the source:
--
--   - generalization: the hedger's information is σ(A_T, X_T), with A_T adapted to the asset filtration F^X and B̃ a Brownian motion independent of B (§3, pp. 10–12) → any sub-σ-algebra G of the probability space such that A_T and B_T are G-measurable and ξ = B̃_T/√T is independent of G; reason: σ(A_T, X_T) = σ(A_T, B_T) (X_T is a strictly increasing function of B_T) satisfies these properties, so the paper's model is the instance G = σ(A_T, X_T); nothing else about G enters the statement
--   - encoding: the dynamic model: GBM asset (17), demand dD_t = dA_t + σ̃dB̃_t (18)–(19), density process (26) on [0, T] → the terminal values only: A_T ≥ 0, W = B_T with law N(0, T), ξ with law N(0, 1); Z_T = exp(−ηW − η²T/2), D_T = A_T + σ̃√T ξ; reason: every object in the statement is a function of (A_T, B_T, B̃_T); B̃_T has the law of √T ξ
--   - reading: p is the unit profit, c the net unit cost (p. 5), σ̃ > 0 (p. 10), T > 0 (p. 5), budget C > 0 (p. 12), η ≠ 0 (p. 13) → hypotheses p > 0, c > 0, σ̃ > 0, T > 0, C > 0, η ≠ 0 (Params.Valid); reason: the standing assumptions of §§2–3; c > 0 is needed: with c = 0 the second equation of (45) has no root, since its left-hand side stays below p(1 − α)
-- source:
--   Wang, Yao, Production Planning with Risk Hedging under a CVaR Objective, SSRN 3875464 (April 2020), p. 19, (49)

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_ProdHedgeCVaR_Joint_Model

namespace ProdHedgeCVaR.Joint

open MeasureTheory ProbabilityTheory Filter Topology

/-- (49), p. 19: if λ° solves the first equation of (45), then
1 − α = E[1 − (1 − λ°Z_T)⁺] = E(1 ∧ λ°Z_T) ≤ λ°E(Z_T) = λ°. -/
theorem eq_49 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (lamC : ℝ) (hlamC : M.IsLamC α lamC) :
    1 - α = ∫ ω, (1 - max (1 - lamC * M.Z ω) 0) ∂M.P ∧
    ∫ ω, (1 - max (1 - lamC * M.Z ω) 0) ∂M.P = ∫ ω, min 1 (lamC * M.Z ω) ∂M.P ∧
    ∫ ω, min 1 (lamC * M.Z ω) ∂M.P ≤ lamC * ∫ ω, M.Z ω ∂M.P ∧
    lamC * ∫ ω, M.Z ω ∂M.P = lamC := by sorry

end ProdHedgeCVaR.Joint
