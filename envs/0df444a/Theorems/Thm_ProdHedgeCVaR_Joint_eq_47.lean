-- Prove2me | Theorems.Thm_ProdHedgeCVaR_Joint_eq_47
-- name    : ProdHedgeCVaR.Joint.eq_47
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:46:04.419521+00:00
-- url     : https://prove2.me/theorems/2db891f6-53ee-4840-85da-bfcd42354e59
-- title:
--   (47)–(48), p. 19 — C° ≤ p(Q°)⁺: C° ≤ (p + c)Q°P^M(λ°Z_T ≤ ∆) ≤ pQ°(1 − α)/λ° ≤ pQ°, using {D̂⁺_T ≤ Q} = {λZ_T ≤ ∆(Q)}
-- statement:
--   Throughout, $(\Omega,\mathcal F,\mathbb P)$ is a probability space carrying the terminal values of the model of §3: the asset-driven demand component $A_T\ge 0$, the asset noise $B_T\sim N(0,T)$, both measurable with respect to the hedger's information $\mathcal G$ (the paper's $\sigma(A_T,X_T)$), and $\xi\sim N(0,1)$ independent of $\mathcal G$. The demand is $D_T=A_T+\tilde\sigma\sqrt T\,\xi$, the production payoff $H_T(Q)=pQ-(p+c)(Q-D_T^+)^+$, and $Z_T=e^{-\eta B_T-\eta^2T/2}$ is the density of the martingale measure, $\mathsf E^M[Y]=\mathsf E[Z_TY]$. The parameters satisfy $p,c,\tilde\sigma,T,C>0$ and $\eta\ne0$. Let $\alpha\in(0,1)$, let $(\lambda^\circ,Q^\circ)$ solve (45), let $C^\circ=(p+c)\,\mathsf E^M[(Q^\circ-\hat D_T^+(\lambda^\circ))^+]$ (46), and write $\Delta=\Delta(Q^\circ)$. Then:
--
--   1. $C^\circ\le p(Q^\circ)^+$.
--   2. If $Q^\circ\le0$, then $C^\circ=p(Q^\circ)^+=0$.
--   3. For every $Q\ge0$ and $\lambda\ge0$, $\{\hat D_T^+(\lambda)\le Q\}=\{\lambda Z_T\le\Delta(Q)\}$.
--   4. If $Q^\circ\ge0$, then
--   $$C^\circ\le(p+c)Q^\circ\,\mathsf P^M(\lambda^\circ Z_T\le\Delta)\le pQ^\circ\frac{1-\alpha}{\lambda^\circ}\le pQ^\circ.\qquad(47)$$
--   5. $$\mathsf E[(\lambda^\circ Z_T)\wedge\Delta]\ge\mathsf E\big[\lambda^\circ Z_T\mathbf 1\{\lambda^\circ Z_T\le\Delta\}\big]=\lambda^\circ\,\mathsf P^M(\lambda^\circ Z_T\le\Delta).\qquad(48)$$
--
--   The bound $C^\circ\le p(Q^\circ)^+$ is what makes $m^\circ\ge0$ in (50).
--
--   Differences from the source:
--
--   - generalization: (48), stated in the case Q° ≥ 0 → (48) for Q° of either sign; reason: (48) does not use the sign of Q°; the paper's case is an instance
--   - encoding: D̂_T of (30) with Φ⁻¹(0) = −∞, Φ⁻¹(1) = +∞; E^M, P^M under dP^M/dP = Z_T (26) → D̂_T(λ) in EReal: −∞ if λZ_T ≤ 0, +∞ if λZ_T ≥ 1, else A_T + σ̃√T Φ⁻¹(λZ_T) with Φ⁻¹(u) = sup{x : Φ(x) ≤ u}; E^M[Y] = E[Z_T Y], P^M(S) = E[Z_T 1_S]; reason: Φ is continuous and strictly increasing onto (0, 1), so the order inverse is Φ⁻¹ there; the endpoint values are the paper's conventions (p. 15); E^M and P^M are the expectations under the measure with density Z_T
--   - generalization: the hedger's information is σ(A_T, X_T), with A_T adapted to the asset filtration F^X and B̃ a Brownian motion independent of B (§3, pp. 10–12) → any sub-σ-algebra G of the probability space such that A_T and B_T are G-measurable and ξ = B̃_T/√T is independent of G; reason: σ(A_T, X_T) = σ(A_T, B_T) (X_T is a strictly increasing function of B_T) satisfies these properties, so the paper's model is the instance G = σ(A_T, X_T); nothing else about G enters the statement
--   - encoding: the dynamic model: GBM asset (17), demand dD_t = dA_t + σ̃dB̃_t (18)–(19), density process (26) on [0, T] → the terminal values only: A_T ≥ 0, W = B_T with law N(0, T), ξ with law N(0, 1); Z_T = exp(−ηW − η²T/2), D_T = A_T + σ̃√T ξ; reason: every object in the statement is a function of (A_T, B_T, B̃_T); B̃_T has the law of √T ξ
--   - reading: p is the unit profit, c the net unit cost (p. 5), σ̃ > 0 (p. 10), T > 0 (p. 5), budget C > 0 (p. 12), η ≠ 0 (p. 13) → hypotheses p > 0, c > 0, σ̃ > 0, T > 0, C > 0, η ≠ 0 (Params.Valid); reason: the standing assumptions of §§2–3; c > 0 is needed: with c = 0 the second equation of (45) has no root, since its left-hand side stays below p(1 − α)
-- source:
--   Wang, Yao, Production Planning with Risk Hedging under a CVaR Objective, SSRN 3875464 (April 2020), p. 19, (46)–(48)

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_ProdHedgeCVaR_Joint_Model

namespace ProdHedgeCVaR.Joint

open MeasureTheory ProbabilityTheory Filter Topology

/-- (47)–(48), p. 19: C° never exceeds p(Q°)⁺; C° = p(Q°)⁺ = 0 when Q° ≤ 0;
{D̂_T⁺(λ) ≤ Q} = {λZ_T ≤ ∆(Q)} for Q ≥ 0; for Q° ≥ 0,
C° ≤ (p + c)Q°P^M(λ°Z_T ≤ ∆) ≤ pQ°(1 − α)/λ° ≤ pQ°; and
E[(λ°Z_T) ∧ ∆] ≥ E[λ°Z_T 1{λ°Z_T ≤ ∆}] = λ°P^M(λ°Z_T ≤ ∆), with ∆ = ∆(Q°). -/
theorem eq_47 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (lamC QC : ℝ)
    (hlamC : M.IsLamC α lamC) (hQC : M.IsQC α lamC QC) :
    M.CC lamC QC ≤ M.θ.p * max QC 0 ∧
    (QC ≤ 0 → M.CC lamC QC = 0 ∧ M.θ.p * max QC 0 = 0) ∧
    (∀ Q lam : ℝ, 0 ≤ Q → 0 ≤ lam →
      {ω | M.DhatPos lam ω ≤ (Q : EReal)} = {ω | lam * M.Z ω ≤ M.Delta Q ω}) ∧
    (0 ≤ QC →
      M.CC lamC QC ≤ (M.θ.p + M.θ.c) * QC * M.PM {ω | lamC * M.Z ω ≤ M.Delta QC ω} ∧
      (M.θ.p + M.θ.c) * QC * M.PM {ω | lamC * M.Z ω ≤ M.Delta QC ω}
        ≤ M.θ.p * QC * (1 - α) / lamC ∧
      M.θ.p * QC * (1 - α) / lamC ≤ M.θ.p * QC) ∧
    (∫ ω, lamC * M.Z ω * (if lamC * M.Z ω ≤ M.Delta QC ω then 1 else 0) ∂M.P
        ≤ ∫ ω, min (lamC * M.Z ω) (M.Delta QC ω) ∂M.P ∧
      ∫ ω, lamC * M.Z ω * (if lamC * M.Z ω ≤ M.Delta QC ω then 1 else 0) ∂M.P
        = lamC * M.PM {ω | lamC * M.Z ω ≤ M.Delta QC ω}) := by sorry

end ProdHedgeCVaR.Joint
