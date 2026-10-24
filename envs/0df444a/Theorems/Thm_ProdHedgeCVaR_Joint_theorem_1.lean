-- Prove2me | Theorems.Thm_ProdHedgeCVaR_Joint_theorem_1
-- name    : ProdHedgeCVaR.Joint.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:45:53.832773+00:00
-- url     : https://prove2.me/theorems/3066633b-e600-479e-8484-4be6ed888816
-- title:
--   Theorem 1, p. 15 — the a.s. unique optimal payoff V*_T of (28) and s(m, Q) as in (34) (corrected: λ solves E^M[V*] = 0, i.e. (35), not E[V*] = 0; λ is unique only when m − pQ + C > 0)
-- statement:
--   Throughout, $(\Omega,\mathcal F,\mathbb P)$ is a probability space carrying the terminal values of the model of §3: the asset-driven demand component $A_T\ge 0$, the asset noise $B_T\sim N(0,T)$, both measurable with respect to the hedger's information $\mathcal G$ (the paper's $\sigma(A_T,X_T)$), and $\xi\sim N(0,1)$ independent of $\mathcal G$. The demand is $D_T=A_T+\tilde\sigma\sqrt T\,\xi$, the production payoff $H_T(Q)=pQ-(p+c)(Q-D_T^+)^+$, and $Z_T=e^{-\eta B_T-\eta^2T/2}$ is the density of the martingale measure, $\mathsf E^M[Y]=\mathsf E[Z_TY]$. The parameters satisfy $p,c,\tilde\sigma,T,C>0$ and $\eta\ne0$. Let $m\ge0$ and $Q\ge0$ with $m-pQ+C\ge0$, and put $K=(m+C+cQ)/(p+c)$. For $\lambda\ge0$ let $\hat D_T(\lambda)=A_T+\tilde\sigma\sqrt T\,\Phi^{-1}(\lambda Z_T)$, equal to $+\infty$ when $\lambda Z_T\ge1$ and $-\infty$ when $\lambda Z_T=0$.
--
--   1. Equation (35),
--   $$(p+c)\Big[(K-Q)\,\mathsf P^M(\lambda Z_T\le1)+\mathsf E^M\big[(Q-\hat D_T^+(\lambda))^+\big]\Big]=C,$$
--   has a solution $\lambda\ge0$, and exactly one when $m-pQ+C>0$.
--   2. For every such $\lambda$, the payoff
--   $$V_T^*(m,Q)=(p+c)\Big[(K-Q)\mathbf 1\{\lambda Z_T\le1\}+\big(Q-\hat D_T^+\big)^+\Big]-C\qquad(33)$$
--   is feasible for the static hedging problem (28) — it is $\mathcal G$-measurable, $V_T^*\ge-C$ and $\mathsf E^M[V_T^*]\le0$ — and in fact $\mathsf E^M[V_T^*]=0$.
--   3. $V_T^*$ is optimal: $\mathsf E[(m-H_T(Q)-V_T^*)^+]=s(m,Q)$, the optimal value of (28); and every feasible $V$ attaining $s(m,Q)$ equals $V_T^*$ almost surely.
--   4. The attained shortfall is
--   $$s(m,Q)=(p+c)\Big[(K-Q)\,\mathsf P(\lambda Z_T\ge1)+\mathsf E\big[(Q\wedge\hat D_T^+-D_T^+)^+\big]\Big].\qquad(34)$$
--
--   The optimal payoff is a short cash position $-C$ plus $p+c$ units of a digital option paying $K-Q$ when $\lambda Z_T\le1$ and $p+c$ units of a put with strike $Q$ on the surrogate demand $\hat D_T$; (34) is the closed form of $s$ that problem (36) maximizes against.
--
--   **Formalization Note** The paper writes "λ is the solution to $\mathsf E[V_T^*(m,Q)]=0$" under the physical measure; the explicit equation (35) it then gives, and Proposition 2, use $\mathsf E^M$, and only the $\mathsf E^M$ version makes $V_T^*$ optimal. The statement uses (35).
--
--   Differences from the source:
--
--   - correction: 'λ is the solution to E[V*_T(m, Q)] = 0' (physical expectation E) → λ ≥ 0 is the solution of (35), equivalently E^M[V*_T] = 0, and the statement includes E^M[V*_T] = 0; reason: with the physical E the constraint E^M V ≤ 0 is slack and V* is not optimal: p = 1, c = 1/2, η = T = σ̃ = C = 1, A_T = 2 + e^{0.3B_T}/2, m = 2.5, Q = 2 gives λ = 1.169 with E^M V* = −0.611 and shortfall 0.831, while (35) gives λ = 0.461 and shortfall 0.382 (missions/_checks/wang2023_physical_E_slip.py); (35) and Proposition 2 already use E^M
--   - reading: '(hence also the optimal hedging payoff of (22))' → not formalized; the statement is about the static problem (28); reason: the parenthetical is Proposition 2 (p. 14), whose proof needs stochastic integrals against the GBM and the martingale representation theorem; it is not part of the proof in §9.1
--   - reading: 'the optimal solution to (28) … is V*_T'; 'λ is the solution to …' → (35) has a root λ ≥ 0 (unique when m − pQ + C > 0, see the correction below); for every root, V*_T is feasible and attains the infimum s(m, Q); every feasible optimizer equals V*_T a.s.; reason: 'the optimal solution' and 'the solution' assert existence and uniqueness; uniqueness of a payoff can only hold up to null sets; λ ≥ 0 is the Lagrange multiplier of E^M V ≤ 0
--   - correction: 'λ is the solution to …' (a unique root of (35) for every admissible (m, Q)) → (35) has a root λ ≥ 0, unique when m − pQ + C > 0, and every conclusion is stated for every root; reason: on the line m − pQ + C = 0 the root can be non-unique: take 0 < λ₁ < λ₂, z₀ > 0 with λ₂z₀ ≤ 1/2 and π := P^M(Z_T ≤ z₀) ≤ p/(p + c), any Q > 0, A_T = 0 on {Z_T ≤ z₀} and A_T = Q − σ̃√T Φ⁻¹(min(λ₁Z_T, 1/2)) on {Z_T > z₀} (a nonnegative function of B_T), C := (p + c)Qπ and m := pQ − C ≥ 0; then K = Q, (Q − D̂⁺_T(λ))⁺ = Q·1{Z_T ≤ z₀} for every λ ∈ [λ₁, λ₂], and every such λ solves (35); V*_T is the same for all of them, so the other conclusions hold for every root; for m − pQ + C > 0 the term (K − Q)P^M(λZ_T ≤ 1) is strictly decreasing in λ and the root is unique
--   - reading: s(m, Q) of (22), 'completely characterized in (34)' (p. 16) → s(m, Q) is the optimal value of the static problem (28): the infimum of E[(m − H_T(Q) − V)⁺] over feasible terminal payoffs V; reason: (36) uses s through (34), which Theorem 1 derives from (28); that (22) and (28) have the same value is Proposition 2 (stochastic integration and martingale representation), not formalized
--   - encoding: (28): V_T a function of (A_T, X_T), V_T ≥ −C, E^M(V_T) ≤ 0 → V is G-measurable, V ≥ −C at every point, Z_T·V is integrable, and E[Z_T V] ≤ 0; reason: integrability is what makes E^M(V) defined; requiring V ≥ −C everywhere rather than a.s. gives the same infimum, since max(V, −C) is G-measurable and equals V a.s.
--   - encoding: D̂_T of (30) with Φ⁻¹(0) = −∞, Φ⁻¹(1) = +∞; E^M, P^M under dP^M/dP = Z_T (26) → D̂_T(λ) in EReal: −∞ if λZ_T ≤ 0, +∞ if λZ_T ≥ 1, else A_T + σ̃√T Φ⁻¹(λZ_T) with Φ⁻¹(u) = sup{x : Φ(x) ≤ u}; E^M[Y] = E[Z_T Y], P^M(S) = E[Z_T 1_S]; reason: Φ is continuous and strictly increasing onto (0, 1), so the order inverse is Φ⁻¹ there; the endpoint values are the paper's conventions (p. 15); E^M and P^M are the expectations under the measure with density Z_T
--   - generalization: the hedger's information is σ(A_T, X_T), with A_T adapted to the asset filtration F^X and B̃ a Brownian motion independent of B (§3, pp. 10–12) → any sub-σ-algebra G of the probability space such that A_T and B_T are G-measurable and ξ = B̃_T/√T is independent of G; reason: σ(A_T, X_T) = σ(A_T, B_T) (X_T is a strictly increasing function of B_T) satisfies these properties, so the paper's model is the instance G = σ(A_T, X_T); nothing else about G enters the statement
--   - encoding: the dynamic model: GBM asset (17), demand dD_t = dA_t + σ̃dB̃_t (18)–(19), density process (26) on [0, T] → the terminal values only: A_T ≥ 0, W = B_T with law N(0, T), ξ with law N(0, 1); Z_T = exp(−ηW − η²T/2), D_T = A_T + σ̃√T ξ; reason: every object in the statement is a function of (A_T, B_T, B̃_T); B̃_T has the law of √T ξ
--   - reading: p is the unit profit, c the net unit cost (p. 5), σ̃ > 0 (p. 10), T > 0 (p. 5), budget C > 0 (p. 12), η ≠ 0 (p. 13) → hypotheses p > 0, c > 0, σ̃ > 0, T > 0, C > 0, η ≠ 0 (Params.Valid); reason: the standing assumptions of §§2–3; c > 0 is needed: with c = 0 the second equation of (45) has no root, since its left-hand side stays below p(1 − α)
-- source:
--   Wang, Yao, Production Planning with Risk Hedging under a CVaR Objective, SSRN 3875464 (April 2020), p. 15, Theorem 1, (33)–(35); proof §9.1, pp. 31–33

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_ProdHedgeCVaR_Joint_Model

namespace ProdHedgeCVaR.Joint

open MeasureTheory ProbabilityTheory Filter Topology

/-- Theorem 1, p. 15 (corrected: λ solves E^M[V*] = 0, i.e. (35)). For m ≥ 0, Q ≥ 0 with
m − pQ + C ≥ 0: (35) has a root λ ≥ 0, unique when m − pQ + C > 0 (on the line m − pQ + C = 0 it
can fail to be unique for some A_T), and for every such root V*_T of (33) is feasible for (28), attains
its optimal value s(m, Q), is the a.s. unique optimizer, satisfies E^M[V*_T] = 0, and s(m, Q) is given
by (34). -/
theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid)
    (m Q : ℝ) (hm : 0 ≤ m) (hQ : 0 ≤ Q) (hmQ : 0 ≤ m - M.θ.p * Q + M.θ.C) :
    (∃ lam, M.Eq35 m Q lam) ∧
    (0 < m - M.θ.p * Q + M.θ.C → ∃! lam, M.Eq35 m Q lam) ∧
    ∀ lam, M.Eq35 m Q lam →
      M.Feasible (M.Vstar m Q lam) ∧
      M.EM (M.Vstar m Q lam) = 0 ∧
      M.shortfall m Q (M.Vstar m Q lam) = M.s m Q ∧
      (∀ V, M.Feasible V → M.shortfall m Q V = M.s m Q → V =ᵐ[M.P] M.Vstar m Q lam) ∧
      M.s m Q = M.formula34 m Q lam := by sorry

end ProdHedgeCVaR.Joint
