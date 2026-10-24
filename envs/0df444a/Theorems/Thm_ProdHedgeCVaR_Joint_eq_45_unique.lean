-- Prove2me | Theorems.Thm_ProdHedgeCVaR_Joint_eq_45_unique
-- name    : ProdHedgeCVaR.Joint.eq_45_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:46:03.449987+00:00
-- url     : https://prove2.me/theorems/815c5629-9aea-4353-97ad-8e157ed03872
-- title:
--   (45), p. 18 — β(λ) = α has a unique root λ° ≥ 0, and (p + c)E[(λ°Z_T) ∧ ∆(Q)] = p(1 − α) has a unique root Q°
-- statement:
--   Throughout, $(\Omega,\mathcal F,\mathbb P)$ is a probability space carrying the terminal values of the model of §3: the asset-driven demand component $A_T\ge 0$, the asset noise $B_T\sim N(0,T)$, both measurable with respect to the hedger's information $\mathcal G$ (the paper's $\sigma(A_T,X_T)$), and $\xi\sim N(0,1)$ independent of $\mathcal G$. The demand is $D_T=A_T+\tilde\sigma\sqrt T\,\xi$, the production payoff $H_T(Q)=pQ-(p+c)(Q-D_T^+)^+$, and $Z_T=e^{-\eta B_T-\eta^2T/2}$ is the density of the martingale measure, $\mathsf E^M[Y]=\mathsf E[Z_TY]$. The parameters satisfy $p,c,\tilde\sigma,T,C>0$ and $\eta\ne0$. Let $\alpha\in(0,1)$, $\beta(\lambda)=\mathsf E[(1-\lambda Z_T)^+]$ and $\Delta(Q)=\Phi\big((Q-A_T)/(\tilde\sigma\sqrt T)\big)$. Consider the optimality equations
--   $$\beta(\lambda)=\alpha,\qquad (p+c)\,\mathsf E[(\lambda Z_T)\wedge\Delta(Q)]=p(1-\alpha).\qquad(45)$$
--
--   1. The first equation has exactly one real solution $\lambda^\circ$, and $\lambda^\circ\ge0$.
--   2. $\beta(0)=1$, $\beta$ is strictly decreasing on $[0,\infty)$, and $\beta(\lambda)\to0$ as $\lambda\to\infty$.
--   3. $\Delta(Q)\to1$ as $Q\to\infty$, pointwise.
--   4. For $\lambda=\lambda^\circ$: the second equation has exactly one solution $Q^\circ$; its left-hand side is strictly increasing in $Q$ and tends to $(p+c)(1-\alpha)$ as $Q\to\infty$; and
--   $$\mathsf E(1\wedge\lambda^\circ Z_T)=\mathsf E[1-(1-\lambda^\circ Z_T)^+]=1-\alpha.$$
--
--   $\lambda^\circ$ and $Q^\circ$ are the candidate multiplier and production quantity of Theorem 2.
--
--   Differences from the source:
--
--   - reading: 'the left hand side of the equation increases to (p + c)(1 − α)' → the left-hand side is strictly increasing in Q (StrictMono) and tends to (p + c)(1 − α); reason: strict increase is what the uniqueness of Q° rests on; it is the stronger of the two readings of 'increases'
--   - encoding: D̂_T of (30) with Φ⁻¹(0) = −∞, Φ⁻¹(1) = +∞; E^M, P^M under dP^M/dP = Z_T (26) → D̂_T(λ) in EReal: −∞ if λZ_T ≤ 0, +∞ if λZ_T ≥ 1, else A_T + σ̃√T Φ⁻¹(λZ_T) with Φ⁻¹(u) = sup{x : Φ(x) ≤ u}; E^M[Y] = E[Z_T Y], P^M(S) = E[Z_T 1_S]; reason: Φ is continuous and strictly increasing onto (0, 1), so the order inverse is Φ⁻¹ there; the endpoint values are the paper's conventions (p. 15); E^M and P^M are the expectations under the measure with density Z_T
--   - generalization: the hedger's information is σ(A_T, X_T), with A_T adapted to the asset filtration F^X and B̃ a Brownian motion independent of B (§3, pp. 10–12) → any sub-σ-algebra G of the probability space such that A_T and B_T are G-measurable and ξ = B̃_T/√T is independent of G; reason: σ(A_T, X_T) = σ(A_T, B_T) (X_T is a strictly increasing function of B_T) satisfies these properties, so the paper's model is the instance G = σ(A_T, X_T); nothing else about G enters the statement
--   - encoding: the dynamic model: GBM asset (17), demand dD_t = dA_t + σ̃dB̃_t (18)–(19), density process (26) on [0, T] → the terminal values only: A_T ≥ 0, W = B_T with law N(0, T), ξ with law N(0, 1); Z_T = exp(−ηW − η²T/2), D_T = A_T + σ̃√T ξ; reason: every object in the statement is a function of (A_T, B_T, B̃_T); B̃_T has the law of √T ξ
--   - reading: p is the unit profit, c the net unit cost (p. 5), σ̃ > 0 (p. 10), T > 0 (p. 5), budget C > 0 (p. 12), η ≠ 0 (p. 13) → hypotheses p > 0, c > 0, σ̃ > 0, T > 0, C > 0, η ≠ 0 (Params.Valid); reason: the standing assumptions of §§2–3; c > 0 is needed: with c = 0 the second equation of (45) has no root, since its left-hand side stays below p(1 − α)
-- source:
--   Wang, Yao, Production Planning with Risk Hedging under a CVaR Objective, SSRN 3875464 (April 2020), p. 18, (45) and the paragraph after it

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_ProdHedgeCVaR_Joint_Model

namespace ProdHedgeCVaR.Joint

open MeasureTheory ProbabilityTheory Filter Topology

/-- (45), p. 18: the first equation β(λ) = α has a unique root λ°, which is non-negative,
because β decreases from 1 to 0 as λ increases from 0 to ∞; for it the second equation has a unique
root Q°, because ∆(Q) → 1 as Q → ∞ and the left-hand side increases to (p + c)(1 − α), since
E(1 ∧ λ°Z_T) = E[1 − (1 − λ°Z_T)⁺] = 1 − α. -/
theorem eq_45_unique {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    (∃! lam, M.IsLamC α lam) ∧
    (∀ lam, M.IsLamC α lam → 0 ≤ lam) ∧
    (M.beta 0 = 1 ∧ StrictAntiOn M.beta (Set.Ici 0) ∧ Tendsto M.beta atTop (𝓝 0)) ∧
    (∀ ω, Tendsto (fun Q => M.Delta Q ω) atTop (𝓝 1)) ∧
    ∀ lam, M.IsLamC α lam →
      (∃! Q, M.IsQC α lam Q) ∧
      StrictMono (fun Q => (M.θ.p + M.θ.c) * ∫ ω, min (lam * M.Z ω) (M.Delta Q ω) ∂M.P) ∧
      Tendsto (fun Q => (M.θ.p + M.θ.c) * ∫ ω, min (lam * M.Z ω) (M.Delta Q ω) ∂M.P) atTop
        (𝓝 ((M.θ.p + M.θ.c) * (1 - α))) ∧
      ∫ ω, min 1 (lam * M.Z ω) ∂M.P = ∫ ω, (1 - max (1 - lam * M.Z ω) 0) ∂M.P ∧
      ∫ ω, (1 - max (1 - lam * M.Z ω) 0) ∂M.P = 1 - α := by sorry

end ProdHedgeCVaR.Joint
