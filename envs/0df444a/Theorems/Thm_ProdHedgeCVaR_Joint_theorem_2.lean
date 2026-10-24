-- Prove2me | Theorems.Thm_ProdHedgeCVaR_Joint_theorem_2
-- name    : ProdHedgeCVaR.Joint.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:46:03.792988+00:00
-- url     : https://prove2.me/theorems/268b18f2-122e-43c9-b34b-e2765fb3774a
-- title:
--   Theorem 2, p. 20 — the unique optimum of (36): ((Q°)⁺, m°) if C ≥ C°; (pQ* − C, Q*) from (53)+(45b) if C ≤ C°; Q* ≥ min(C, C°)/p (corrected: λ* need not be the only root of (35) when C ≤ C°)
-- statement:
--   Throughout, $(\Omega,\mathcal F,\mathbb P)$ is a probability space carrying the terminal values of the model of §3: the asset-driven demand component $A_T\ge 0$, the asset noise $B_T\sim N(0,T)$, both measurable with respect to the hedger's information $\mathcal G$ (the paper's $\sigma(A_T,X_T)$), and $\xi\sim N(0,1)$ independent of $\mathcal G$. The demand is $D_T=A_T+\tilde\sigma\sqrt T\,\xi$, the production payoff $H_T(Q)=pQ-(p+c)(Q-D_T^+)^+$, and $Z_T=e^{-\eta B_T-\eta^2T/2}$ is the density of the martingale measure, $\mathsf E^M[Y]=\mathsf E[Z_TY]$. The parameters satisfy $p,c,\tilde\sigma,T,C>0$ and $\eta\ne0$. Let $\alpha\in(0,1)$ and let $s(m,Q)$ be the optimal shortfall of the static hedging problem (28). Problem (36) is
--   $$\mathrm{CVaR}^*_\alpha=\max_{m\ge0,\,Q\ge0}\Big\{m-\frac{1}{1-\alpha}\,s(m,Q)\Big\}\quad\text{s.t. } m-pQ+C\ge0.$$
--
--   1. The optimality equations (45), $\mathsf E[(1-\lambda Z_T)^+]=\alpha$ and $(p+c)\,\mathsf E[(\lambda Z_T)\wedge\Delta(Q)]=p(1-\alpha)$, have a unique solution: the first has exactly one root $\lambda^\circ$, and for it the second has exactly one root $Q^\circ$.
--
--   Let $C^\circ=(p+c)\,\mathsf E^M[(Q^\circ-\hat D_T^+(\lambda^\circ))^+]$ (46) and $m^\circ=p(Q^\circ)^+-C+(C-C^\circ)/\mathsf P^M(\lambda^\circ Z_T\le1)$ (50).
--
--   2. **Case (i).** If $C\ge C^\circ$, then (36) has exactly one optimal solution, $(m^*_\alpha,Q^*_\alpha)=(m^\circ,(Q^\circ)^+)$, and the multiplier of (35) at this point is $\lambda^*_\alpha=\lambda^\circ$: $\lambda^\circ$ solves (35) at $(m^\circ,(Q^\circ)^+)$, and when $C>C^\circ$ it is the only $\lambda\ge0$ that does.
--   3. **Case (ii).** If $C\le C^\circ$, then the system formed by (53), $(p+c)\,\mathsf E^M[(Q-\hat D_T^+(\lambda))^+]=C$, and the second equation of (45) has exactly one solution $(\lambda^*_\alpha,Q^*_\alpha)$ with $\lambda^*_\alpha\ge0$; problem (36) has exactly one optimal solution, $(pQ^*_\alpha-C,\,Q^*_\alpha)$; $\lambda^*_\alpha$ solves (35) there; and
--   $$\lambda^*_\alpha\ge\lambda^\circ,\qquad Q^*_\alpha\le Q^\circ.$$
--   4. In both cases every optimal solution has
--   $$Q^*_\alpha\ge\frac{C\wedge C^\circ}{p}.$$
--
--   This is the paper's solution of the joint production and hedging problem: the optimal capacity, the CVaR target, and (through Theorem 1) the optimal hedge, with the hedging budget either slack ($C\ge C^\circ$) or binding.
--
--   Differences from the source:
--
--   - reading: 'let (m*_α, Q*_α) be the optimal solution to (36)'; 'to obtain λ*_α and Q*_α' → the set of optimal solutions of (36) is the singleton named in each case, and the (53)+(45) system has a unique solution (∃!); reason: 'the optimal solution' and 'to obtain' presuppose existence and uniqueness; a statement about an assumed optimizer alone would be weaker
--   - correction: λ*_α, the multiplier at the optimum, read as the root of (35) there (Theorem 1's 'λ is the solution to (35)') → λ° (case (i)) and λ*_α (case (ii)) solve (35) at the optimum, and λ° is its only root when C > C°; reason: when the budget binds the root of (35) at the optimum can be non-unique: in case (ii) take λ° ≤ λ₁ < λ* < λ₂, z₀ > 0 with λ₂z₀ ≤ 1/2, a large Q* > 0, A_T = 0 on {Z_T ≤ z₀} and A_T = Q* − σ̃√T Φ⁻¹(κ min(λ₁Z_T, 1)) on {Z_T > z₀}, with κ ∈ (0, Φ(Q*/(σ̃√T))] chosen so that the second equation of (45) holds at (λ*, Q*), and C := (p + c)Q*P^M(Z_T ≤ z₀) (small z₀ makes pQ* − C ≥ 0); then (λ*, Q*) solves (53) and the second equation of (45), C ≤ C° holds automatically, and since (Q* − D̂⁺_T(λ))⁺ = Q*·1{Z_T ≤ z₀} for every λ ∈ [λ₁, λ₂], every such λ solves (35) at (pQ* − C, Q*); for C > C° the point (m°, (Q°)⁺) has K − Q = (C − C°)/((p + c)P^M(λ°Z_T ≤ 1)) > 0 and the root is unique
--   - reading: s(m, Q) of (22), 'completely characterized in (34)' (p. 16) → s(m, Q) is the optimal value of the static problem (28): the infimum of E[(m − H_T(Q) − V)⁺] over feasible terminal payoffs V; reason: (36) uses s through (34), which Theorem 1 derives from (28); that (22) and (28) have the same value is Proposition 2 (stochastic integration and martingale representation), not formalized
--   - encoding: (28): V_T a function of (A_T, X_T), V_T ≥ −C, E^M(V_T) ≤ 0 → V is G-measurable, V ≥ −C at every point, Z_T·V is integrable, and E[Z_T V] ≤ 0; reason: integrability is what makes E^M(V) defined; requiring V ≥ −C everywhere rather than a.s. gives the same infimum, since max(V, −C) is G-measurable and equals V a.s.
--   - encoding: D̂_T of (30) with Φ⁻¹(0) = −∞, Φ⁻¹(1) = +∞; E^M, P^M under dP^M/dP = Z_T (26) → D̂_T(λ) in EReal: −∞ if λZ_T ≤ 0, +∞ if λZ_T ≥ 1, else A_T + σ̃√T Φ⁻¹(λZ_T) with Φ⁻¹(u) = sup{x : Φ(x) ≤ u}; E^M[Y] = E[Z_T Y], P^M(S) = E[Z_T 1_S]; reason: Φ is continuous and strictly increasing onto (0, 1), so the order inverse is Φ⁻¹ there; the endpoint values are the paper's conventions (p. 15); E^M and P^M are the expectations under the measure with density Z_T
--   - generalization: the hedger's information is σ(A_T, X_T), with A_T adapted to the asset filtration F^X and B̃ a Brownian motion independent of B (§3, pp. 10–12) → any sub-σ-algebra G of the probability space such that A_T and B_T are G-measurable and ξ = B̃_T/√T is independent of G; reason: σ(A_T, X_T) = σ(A_T, B_T) (X_T is a strictly increasing function of B_T) satisfies these properties, so the paper's model is the instance G = σ(A_T, X_T); nothing else about G enters the statement
--   - encoding: the dynamic model: GBM asset (17), demand dD_t = dA_t + σ̃dB̃_t (18)–(19), density process (26) on [0, T] → the terminal values only: A_T ≥ 0, W = B_T with law N(0, T), ξ with law N(0, 1); Z_T = exp(−ηW − η²T/2), D_T = A_T + σ̃√T ξ; reason: every object in the statement is a function of (A_T, B_T, B̃_T); B̃_T has the law of √T ξ
--   - reading: p is the unit profit, c the net unit cost (p. 5), σ̃ > 0 (p. 10), T > 0 (p. 5), budget C > 0 (p. 12), η ≠ 0 (p. 13) → hypotheses p > 0, c > 0, σ̃ > 0, T > 0, C > 0, η ≠ 0 (Params.Valid); reason: the standing assumptions of §§2–3; c > 0 is needed: with c = 0 the second equation of (45) has no root, since its left-hand side stays below p(1 − α)
-- source:
--   Wang, Yao, Production Planning with Risk Hedging under a CVaR Objective, SSRN 3875464 (April 2020), p. 20, Theorem 2

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_ProdHedgeCVaR_Joint_Model

namespace ProdHedgeCVaR.Joint

open MeasureTheory ProbabilityTheory Filter Topology

/-- Theorem 2, p. 20. Given α ∈ (0, 1): λ° and Q° (the solutions of (45)) exist uniquely, and,
with C° from (46) and m° from (50):
(i) if C ≥ C°, the optimal solution of (36) is unique and equals (m°, (Q°)⁺), and λ*_α = λ° solves
(35) there (its only root when C > C°);
(ii) if C ≤ C°, the system (53) + second equation of (45) has a unique solution (λ*_α, Q*_α), the
optimal solution of (36) is unique and equals (pQ*_α − C, Q*_α), λ*_α solves (35) there, and
λ*_α ≥ λ°, Q*_α ≤ Q°;
in both cases every optimal Q*_α satisfies Q*_α ≥ (C ∧ C°)/p. -/
theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    (∃! lam, M.IsLamC α lam) ∧ (∀ lam, M.IsLamC α lam → ∃! Q, M.IsQC α lam Q) ∧
    ∀ lamC QC, M.IsLamC α lamC → M.IsQC α lamC QC →
      (M.CC lamC QC ≤ M.θ.C →
        {x | M.IsOptimal36 α x} = {(M.mC lamC QC, max QC 0)} ∧
        M.Eq35 (M.mC lamC QC) (max QC 0) lamC ∧
        (M.CC lamC QC < M.θ.C → ∀ lam, M.Eq35 (M.mC lamC QC) (max QC 0) lam ↔ lam = lamC)) ∧
      (M.θ.C ≤ M.CC lamC QC →
        (∃! y : ℝ × ℝ, 0 ≤ y.1 ∧ M.Eq53 y.1 y.2 ∧ M.IsQC α y.1 y.2) ∧
        ∀ lamS QS, 0 ≤ lamS → M.Eq53 lamS QS → M.IsQC α lamS QS →
          {x | M.IsOptimal36 α x} = {(M.θ.p * QS - M.θ.C, QS)} ∧
          M.Eq35 (M.θ.p * QS - M.θ.C) QS lamS ∧
          lamC ≤ lamS ∧ QS ≤ QC) ∧
      (∀ x, M.IsOptimal36 α x → min M.θ.C (M.CC lamC QC) / M.θ.p ≤ x.2) := by sorry

end ProdHedgeCVaR.Joint
