-- Prove2me | Theorems.Thm_ProdHedgeCVaR_Joint_lemma_5
-- name    : ProdHedgeCVaR.Joint.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:45:56.534709+00:00
-- url     : https://prove2.me/theorems/1c63424a-4fd0-4c90-8d09-653b345c9a02
-- title:
--   Lemma 5, p. 17 — P(D_T ≤ D̂_T) = 1 − β = λ − ψ, λP^M(λZ_T ≤ 1) + P(λZ_T ≥ 1) = 1 − β (38), and P(𝒟) = E[(λZ_T) ∧ ∆] (39)
-- statement:
--   Throughout, $(\Omega,\mathcal F,\mathbb P)$ is a probability space carrying the terminal values of the model of §3: the asset-driven demand component $A_T\ge 0$, the asset noise $B_T\sim N(0,T)$, both measurable with respect to the hedger's information $\mathcal G$ (the paper's $\sigma(A_T,X_T)$), and $\xi\sim N(0,1)$ independent of $\mathcal G$. The demand is $D_T=A_T+\tilde\sigma\sqrt T\,\xi$, the production payoff $H_T(Q)=pQ-(p+c)(Q-D_T^+)^+$, and $Z_T=e^{-\eta B_T-\eta^2T/2}$ is the density of the martingale measure, $\mathsf E^M[Y]=\mathsf E[Z_TY]$. The parameters satisfy $p,c,\tilde\sigma,T,C>0$ and $\eta\ne0$. Fix $\lambda\ge0$ and a real number $Q$. Let $\hat D_T=\hat D_T(\lambda)$ be as in (30) (with $\hat D_T=+\infty$ when $\lambda Z_T\ge1$ and $-\infty$ when $\lambda Z_T=0$), $\beta=\mathsf E[(1-\lambda Z_T)^+]$ and $\psi=\mathsf E[(\lambda Z_T-1)^+]$ (37), $\Delta=\Phi\big((Q-A_T)/(\tilde\sigma\sqrt T)\big)$ (29), and $\mathcal D=\{D_T\le Q\wedge\hat D_T\}$. Then
--   $$\mathsf P(D_T\le\hat D_T)=1-\beta=\lambda-\psi,\qquad \lambda\,\mathsf P^M(\lambda Z_T\le1)+\mathsf P(\lambda Z_T\ge1)=1-\beta,\qquad(38)$$
--   and
--   $$\mathsf P(\mathcal D)=\mathsf P\Big(\xi\le\Phi^{-1}(\lambda Z_T)\wedge\frac{Q-A_T}{\tilde\sigma\sqrt T}\Big)=\mathsf E[(\lambda Z_T)\wedge\Delta].\qquad(39)$$
--
--   These identities convert the closed form (34) into the expression (42) for $s(m,Q)$ from which the optimality equations are derived.
--
--   Differences from the source:
--
--   - generalization: Q the production quantity (Q ≥ 0 in context) → every real Q; reason: the identities (39) hold for every real Q; the paper's case Q ≥ 0 is an instance
--   - encoding: P(ξ ≤ Φ⁻¹(λZ_T) ∧ (Q − A_T)/(σ̃√T)) with Φ⁻¹ possibly ±∞ → the comparison is made in EReal; reason: Φ⁻¹(λZ_T) is ±∞ at the endpoints; the event is the same
--   - encoding: D̂_T of (30) with Φ⁻¹(0) = −∞, Φ⁻¹(1) = +∞; E^M, P^M under dP^M/dP = Z_T (26) → D̂_T(λ) in EReal: −∞ if λZ_T ≤ 0, +∞ if λZ_T ≥ 1, else A_T + σ̃√T Φ⁻¹(λZ_T) with Φ⁻¹(u) = sup{x : Φ(x) ≤ u}; E^M[Y] = E[Z_T Y], P^M(S) = E[Z_T 1_S]; reason: Φ is continuous and strictly increasing onto (0, 1), so the order inverse is Φ⁻¹ there; the endpoint values are the paper's conventions (p. 15); E^M and P^M are the expectations under the measure with density Z_T
--   - generalization: the hedger's information is σ(A_T, X_T), with A_T adapted to the asset filtration F^X and B̃ a Brownian motion independent of B (§3, pp. 10–12) → any sub-σ-algebra G of the probability space such that A_T and B_T are G-measurable and ξ = B̃_T/√T is independent of G; reason: σ(A_T, X_T) = σ(A_T, B_T) (X_T is a strictly increasing function of B_T) satisfies these properties, so the paper's model is the instance G = σ(A_T, X_T); nothing else about G enters the statement
--   - encoding: the dynamic model: GBM asset (17), demand dD_t = dA_t + σ̃dB̃_t (18)–(19), density process (26) on [0, T] → the terminal values only: A_T ≥ 0, W = B_T with law N(0, T), ξ with law N(0, 1); Z_T = exp(−ηW − η²T/2), D_T = A_T + σ̃√T ξ; reason: every object in the statement is a function of (A_T, B_T, B̃_T); B̃_T has the law of √T ξ
--   - reading: p is the unit profit, c the net unit cost (p. 5), σ̃ > 0 (p. 10), T > 0 (p. 5), budget C > 0 (p. 12), η ≠ 0 (p. 13) → hypotheses p > 0, c > 0, σ̃ > 0, T > 0, C > 0, η ≠ 0 (Params.Valid); reason: the standing assumptions of §§2–3; c > 0 is needed: with c = 0 the second equation of (45) has no root, since its left-hand side stays below p(1 − α)
-- source:
--   Wang, Yao, Production Planning with Risk Hedging under a CVaR Objective, SSRN 3875464 (April 2020), p. 17, Lemma 5, (37)–(39)

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_ProdHedgeCVaR_Joint_Model

namespace ProdHedgeCVaR.Joint

open MeasureTheory ProbabilityTheory Filter Topology

/-- Lemma 5, p. 17: (38) and (39), for every λ ≥ 0 and every Q. -/
theorem lemma_5 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid)
    (lam : ℝ) (hlam : 0 ≤ lam) (Q : ℝ) :
    M.P.real {ω | ((M.D ω : ℝ) : EReal) ≤ M.Dhat lam ω} = 1 - M.beta lam ∧
    1 - M.beta lam = lam - M.psi lam ∧
    lam * M.PM {ω | lam * M.Z ω ≤ 1} + M.P.real {ω | 1 ≤ lam * M.Z ω} = 1 - M.beta lam ∧
    M.P.real (M.Dset lam Q) =
      M.P.real {ω | ((M.xi ω : ℝ) : EReal) ≤
        min (stdNormalInvE (lam * M.Z ω))
          (((Q - M.A ω) / (M.θ.sigT * Real.sqrt M.θ.T) : ℝ) : EReal)} ∧
    M.P.real {ω | ((M.xi ω : ℝ) : EReal) ≤
        min (stdNormalInvE (lam * M.Z ω))
          (((Q - M.A ω) / (M.θ.sigT * Real.sqrt M.θ.T) : ℝ) : EReal)} =
      ∫ ω, min (lam * M.Z ω) (M.Delta Q ω) ∂M.P := by sorry

end ProdHedgeCVaR.Joint
