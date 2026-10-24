-- Prove2me | Theorems.Thm_ProdHedgeCVaR_Joint_eq_53_system
-- name    : ProdHedgeCVaR.Joint.eq_53_system
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:46:06.729751+00:00
-- url     : https://prove2.me/theorems/2a980b07-117b-40b0-bade-4b3f690749a7
-- title:
--   (53), p. 20 — for C ≤ C°, (53) with the second equation of (45) has a unique solution (λ, Q), and pQ ≥ C (corrected: the left side of (53) is weakly, not strictly, monotone)
-- statement:
--   Throughout, $(\Omega,\mathcal F,\mathbb P)$ is a probability space carrying the terminal values of the model of §3: the asset-driven demand component $A_T\ge 0$, the asset noise $B_T\sim N(0,T)$, both measurable with respect to the hedger's information $\mathcal G$ (the paper's $\sigma(A_T,X_T)$), and $\xi\sim N(0,1)$ independent of $\mathcal G$. The demand is $D_T=A_T+\tilde\sigma\sqrt T\,\xi$, the production payoff $H_T(Q)=pQ-(p+c)(Q-D_T^+)^+$, and $Z_T=e^{-\eta B_T-\eta^2T/2}$ is the density of the martingale measure, $\mathsf E^M[Y]=\mathsf E[Z_TY]$. The parameters satisfy $p,c,\tilde\sigma,T,C>0$ and $\eta\ne0$. Let $\alpha\in(0,1)$, let $(\lambda^\circ,Q^\circ)$ solve (45), let $C^\circ$ be as in (46), and assume $C\le C^\circ$. Consider the system
--   $$(p+c)\,\mathsf E^M\big[(Q-\hat D_T^+(\lambda))^+\big]=C,\qquad(53)\qquad (p+c)\,\mathsf E[(\lambda Z_T)\wedge\Delta(Q)]=p(1-\alpha).$$
--
--   1. The system has exactly one solution $(\lambda,Q)$ with $\lambda\ge0$.
--   2. Every such solution satisfies $pQ\ge C$, hence $m=pQ-C\ge0$ and $Q\ge0$.
--   3. The left-hand side of (53) is non-decreasing in $Q$ for each $\lambda\ge0$, and non-increasing in $\lambda\ge0$ for each $Q$.
--
--   The solution is the pair $(\lambda^*_\alpha,Q^*_\alpha)$ of case (ii) of Theorem 2.
--
--   Differences from the source:
--
--   - correction: 'must lead to unique solutions to Q and λ, as its left hand side is increasing in Q and decreasing in λ' (strictly, as a uniqueness argument needs) → ∃! (λ, Q) with λ ≥ 0, stated directly; the left-hand side of (53) is non-decreasing in Q for each λ ≥ 0 and non-increasing in λ ≥ 0 for each Q; reason: strict monotonicity fails for some admissible A_T: take A_T = (1 − σ̃√T Φ⁻¹(Z_T))⁺ on {Z_T < 1} and A_T = 0 elsewhere (a nonnegative function of B_T); then D̂_T(λ) ≥ 1 for every λ ≥ 1, so the left-hand side of (53) is 0 for all Q ∈ [0, 1] at λ = 1, and for all λ ≥ 1 at Q = 1/2 (for any α with C° > 0, taking C := C°); the uniqueness the sentence infers still holds and is the first clause
--   - encoding: the second optimality equation in (52) → the second equation of (45) (IsQC); reason: the two equations are identical (p. 20, 'the second equation in (45) stays unchanged')
--   - encoding: D̂_T of (30) with Φ⁻¹(0) = −∞, Φ⁻¹(1) = +∞; E^M, P^M under dP^M/dP = Z_T (26) → D̂_T(λ) in EReal: −∞ if λZ_T ≤ 0, +∞ if λZ_T ≥ 1, else A_T + σ̃√T Φ⁻¹(λZ_T) with Φ⁻¹(u) = sup{x : Φ(x) ≤ u}; E^M[Y] = E[Z_T Y], P^M(S) = E[Z_T 1_S]; reason: Φ is continuous and strictly increasing onto (0, 1), so the order inverse is Φ⁻¹ there; the endpoint values are the paper's conventions (p. 15); E^M and P^M are the expectations under the measure with density Z_T
--   - generalization: the hedger's information is σ(A_T, X_T), with A_T adapted to the asset filtration F^X and B̃ a Brownian motion independent of B (§3, pp. 10–12) → any sub-σ-algebra G of the probability space such that A_T and B_T are G-measurable and ξ = B̃_T/√T is independent of G; reason: σ(A_T, X_T) = σ(A_T, B_T) (X_T is a strictly increasing function of B_T) satisfies these properties, so the paper's model is the instance G = σ(A_T, X_T); nothing else about G enters the statement
--   - encoding: the dynamic model: GBM asset (17), demand dD_t = dA_t + σ̃dB̃_t (18)–(19), density process (26) on [0, T] → the terminal values only: A_T ≥ 0, W = B_T with law N(0, T), ξ with law N(0, 1); Z_T = exp(−ηW − η²T/2), D_T = A_T + σ̃√T ξ; reason: every object in the statement is a function of (A_T, B_T, B̃_T); B̃_T has the law of √T ξ
--   - reading: p is the unit profit, c the net unit cost (p. 5), σ̃ > 0 (p. 10), T > 0 (p. 5), budget C > 0 (p. 12), η ≠ 0 (p. 13) → hypotheses p > 0, c > 0, σ̃ > 0, T > 0, C > 0, η ≠ 0 (Params.Valid); reason: the standing assumptions of §§2–3; c > 0 is needed: with c = 0 the second equation of (45) has no root, since its left-hand side stays below p(1 − α)
-- source:
--   Wang, Yao, Production Planning with Risk Hedging under a CVaR Objective, SSRN 3875464 (April 2020), p. 20, (53) and the paragraph after it

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_ProdHedgeCVaR_Joint_Model

namespace ProdHedgeCVaR.Joint

open MeasureTheory ProbabilityTheory Filter Topology

/-- (53), p. 20: when C ≤ C°, (53) together with the second equation of (45) has a unique
solution (λ, Q) with λ ≥ 0; every solution has pQ ≥ C, hence m = pQ − C ≥ 0 and Q ≥ 0; and the
left-hand side of (53) is non-decreasing in Q (each λ ≥ 0) and non-increasing in λ ≥ 0 (each Q).
Strict monotonicity, which the page's wording may suggest, fails for some admissible A_T. -/
theorem eq_53_system {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (lamC QC : ℝ)
    (hlamC : M.IsLamC α lamC) (hQC : M.IsQC α lamC QC) (hC : M.θ.C ≤ M.CC lamC QC) :
    (∃! y : ℝ × ℝ, 0 ≤ y.1 ∧ M.Eq53 y.1 y.2 ∧ M.IsQC α y.1 y.2) ∧
    (∀ y : ℝ × ℝ, 0 ≤ y.1 → M.Eq53 y.1 y.2 → M.IsQC α y.1 y.2 →
      M.θ.C ≤ M.θ.p * y.2 ∧ 0 ≤ M.θ.p * y.2 - M.θ.C ∧ 0 ≤ y.2) ∧
    (∀ lam : ℝ, 0 ≤ lam →
      Monotone (fun Q => (M.θ.p + M.θ.c) * M.EM (M.putHat lam Q))) ∧
    (∀ Q : ℝ,
      AntitoneOn (fun lam => (M.θ.p + M.θ.c) * M.EM (M.putHat lam Q)) (Set.Ici 0)) := by sorry

end ProdHedgeCVaR.Joint
