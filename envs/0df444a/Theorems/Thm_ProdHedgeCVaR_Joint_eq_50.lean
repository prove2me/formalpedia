-- Prove2me | Theorems.Thm_ProdHedgeCVaR_Joint_eq_50
-- name    : ProdHedgeCVaR.Joint.eq_50
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:45:55.497979+00:00
-- url     : https://prove2.me/theorems/a530c9fd-a7f7-4b60-9e5c-2601c70dad3c
-- title:
--   (50), p. 19 — (35) at (Q°)⁺, λ° has the unique root m° = p(Q°)⁺ − C + (C − C°)/P^M(λ°Z_T ≤ 1); for C ≥ C°, m° ≥ 0 and m° − p(Q°)⁺ + C ≥ 0
-- statement:
--   Throughout, $(\Omega,\mathcal F,\mathbb P)$ is a probability space carrying the terminal values of the model of §3: the asset-driven demand component $A_T\ge 0$, the asset noise $B_T\sim N(0,T)$, both measurable with respect to the hedger's information $\mathcal G$ (the paper's $\sigma(A_T,X_T)$), and $\xi\sim N(0,1)$ independent of $\mathcal G$. The demand is $D_T=A_T+\tilde\sigma\sqrt T\,\xi$, the production payoff $H_T(Q)=pQ-(p+c)(Q-D_T^+)^+$, and $Z_T=e^{-\eta B_T-\eta^2T/2}$ is the density of the martingale measure, $\mathsf E^M[Y]=\mathsf E[Z_TY]$. The parameters satisfy $p,c,\tilde\sigma,T,C>0$ and $\eta\ne0$. Let $\alpha\in(0,1)$, let $(\lambda^\circ,Q^\circ)$ solve (45), and let $C^\circ$ be as in (46). Then:
--
--   1. Equation (35) with $Q=(Q^\circ)^+$ and $\lambda=\lambda^\circ$ has exactly one solution $m$, namely
--   $$m^\circ=p(Q^\circ)^+-C+\frac{C-C^\circ}{\mathsf P^M(\lambda^\circ Z_T\le1)};\qquad(50)$$
--   2. $m^\circ=p(Q^\circ)^+-C^\circ+(C-C^\circ)\Big(\dfrac{1}{\mathsf P^M(\lambda^\circ Z_T\le1)}-1\Big)$;
--   3. if $C\ge C^\circ$, then $m^\circ\ge0$ and
--   4. $m^\circ-p(Q^\circ)^++C\ge0$, so $(m^\circ,(Q^\circ)^+)$ is feasible for (36).
--
--   This is the target level of case (i) of Theorem 2.
--
--   Differences from the source:
--
--   - reading: 'the solution to m from (35), denoted m°' → every m satisfying (35) at Q = (Q°)⁺, λ = λ° equals m°, and m° satisfies it; reason: 'the solution' asserts existence and uniqueness
--   - encoding: D̂_T of (30) with Φ⁻¹(0) = −∞, Φ⁻¹(1) = +∞; E^M, P^M under dP^M/dP = Z_T (26) → D̂_T(λ) in EReal: −∞ if λZ_T ≤ 0, +∞ if λZ_T ≥ 1, else A_T + σ̃√T Φ⁻¹(λZ_T) with Φ⁻¹(u) = sup{x : Φ(x) ≤ u}; E^M[Y] = E[Z_T Y], P^M(S) = E[Z_T 1_S]; reason: Φ is continuous and strictly increasing onto (0, 1), so the order inverse is Φ⁻¹ there; the endpoint values are the paper's conventions (p. 15); E^M and P^M are the expectations under the measure with density Z_T
--   - generalization: the hedger's information is σ(A_T, X_T), with A_T adapted to the asset filtration F^X and B̃ a Brownian motion independent of B (§3, pp. 10–12) → any sub-σ-algebra G of the probability space such that A_T and B_T are G-measurable and ξ = B̃_T/√T is independent of G; reason: σ(A_T, X_T) = σ(A_T, B_T) (X_T is a strictly increasing function of B_T) satisfies these properties, so the paper's model is the instance G = σ(A_T, X_T); nothing else about G enters the statement
--   - encoding: the dynamic model: GBM asset (17), demand dD_t = dA_t + σ̃dB̃_t (18)–(19), density process (26) on [0, T] → the terminal values only: A_T ≥ 0, W = B_T with law N(0, T), ξ with law N(0, 1); Z_T = exp(−ηW − η²T/2), D_T = A_T + σ̃√T ξ; reason: every object in the statement is a function of (A_T, B_T, B̃_T); B̃_T has the law of √T ξ
--   - reading: p is the unit profit, c the net unit cost (p. 5), σ̃ > 0 (p. 10), T > 0 (p. 5), budget C > 0 (p. 12), η ≠ 0 (p. 13) → hypotheses p > 0, c > 0, σ̃ > 0, T > 0, C > 0, η ≠ 0 (Params.Valid); reason: the standing assumptions of §§2–3; c > 0 is needed: with c = 0 the second equation of (45) has no root, since its left-hand side stays below p(1 − α)
-- source:
--   Wang, Yao, Production Planning with Risk Hedging under a CVaR Objective, SSRN 3875464 (April 2020), p. 19, (50) and the lines before it

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_ProdHedgeCVaR_Joint_Model

namespace ProdHedgeCVaR.Joint

open MeasureTheory ProbabilityTheory Filter Topology

/-- (50), p. 19: the solution m of (35) with Q = (Q°)⁺ and λ = λ° is unique and
equals m° = p(Q°)⁺ − C + (C − C°)/P^M(λ°Z_T ≤ 1)
    = p(Q°)⁺ − C° + (C − C°)(1/P^M(λ°Z_T ≤ 1) − 1);
if C ≥ C°, then m° ≥ 0 and the constraint m° − p(Q°)⁺ + C ≥ 0 of (36) is met. -/
theorem eq_50 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (lamC QC : ℝ)
    (hlamC : M.IsLamC α lamC) (hQC : M.IsQC α lamC QC) :
    (∀ m, M.Eq35 m (max QC 0) lamC ↔ m = M.mC lamC QC) ∧
    M.mC lamC QC = M.θ.p * max QC 0 - M.CC lamC QC
      + (M.θ.C - M.CC lamC QC) * (1 / M.PM {ω | lamC * M.Z ω ≤ 1} - 1) ∧
    (M.CC lamC QC ≤ M.θ.C →
      0 ≤ M.mC lamC QC ∧ 0 ≤ M.mC lamC QC - M.θ.p * max QC 0 + M.θ.C) := by sorry

end ProdHedgeCVaR.Joint
