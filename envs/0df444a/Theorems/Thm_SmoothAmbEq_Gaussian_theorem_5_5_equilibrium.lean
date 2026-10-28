-- Prove2me | Theorems.Thm_SmoothAmbEq_Gaussian_theorem_5_5_equilibrium
-- name    : SmoothAmbEq.Gaussian.theorem_5_5_equilibrium
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-24T19:08:35.470666+00:00
-- url     : https://prove2.me/theorems/9e10cbf2-547f-48e5-aed2-c8b22159db1f
-- title:
--   Theorem 5.5, p. 19 (first assertion) — π* of (5.12) is an equilibrium strategy
-- statement:
--   Consider the Gaussian-prior model: $dS_t/S_t=Z\,dt+\sigma\,dW_t$ with $Z\sim N(\beta_0,\sigma_0^2)$, CARA utility $U(x)=-\frac1ke^{-kx}$ and ambiguity function $\phi(u)=-\frac1\alpha(-u)^\alpha$ ($\alpha\ne0$), $\phi(u)=-\log(-u)$ ($\alpha=0$). Let $\alpha^*<0$ be the critical exponent of Proposition 5.4 and assume
--   $$\alpha>\max\Big\{\alpha^*,\ 1-0.5\,\sigma_0^{-2}\sigma^2T^{-1}\Big\}.$$
--   Let $(m_1,\dots,m_6)$ solve the ODE system (5.10) on $[0,T]$ (with $\zeta(t)^{-1}-\alpha m_3(t)>0$), and let
--   $$\pi^*(t,x,\beta)=\frac{e^{-r(T-t)}}{k\sigma^2}\big\{a_1(t,m_2(t),m_3(t))+\zeta(t)m_1(t)\big\}(\beta-r).\qquad(5.12)$$
--   Then $\pi^*$ is an equilibrium strategy in the sense of Definition 2.1, with the admissible class $\Pi$ of Definition 5.1: $\pi^*\in\Pi$, and for every $(t,x,\beta)\in[0,T)\times\mathbb R^2$ and every $\pi\in\Pi$ whose spike variations $\pi_{t,h}$ are admissible for small $h>0$,
--   $$\limsup_{h\to0^+}\frac{J(t,x,\beta,\pi_{t,h})-J(t,x,\beta,\pi^*)}{h}\le0 .$$
--
--   This is the first of the two assertions of Theorem 5.5, the paper's main result; the second assertion (the inside value function equals $g^z$ of (5.8)–(5.9)) follows from it together with the martingale property of Appendix G, Step 1.
--
--   **Formalization Note.** The statement holds on every probability space carrying a Brownian motion; the equilibrium predicate `IsEquilibrium` includes finiteness of $J$ for $\pi^*$ and for small spikes, and the $\limsup$ is in $\varepsilon$-form (same conventions as the mission's goal theorem `SmoothAmbEq.Gaussian.theorem_5_5`, whose first conjunct this is).
-- source:
--   Guan, Liang, Xia, Equilibrium Portfolio Selection for Smooth Ambiguity Preferences, arXiv:2302.08181v1, p. 19, Theorem 5.5 (first assertion: π* is an equilibrium strategy); proof in Appendix G

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_InsideSystem
import Definitions.Def_SmoothAmbEq_Gaussian_Equilibrium
import Definitions.Def_SmoothAmbEq_Gaussian_Candidate

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace SmoothAmbEq.Gaussian

/-- Theorem 5.5, p. 19, first assertion. Assume `α > max{α*, 1 - 0.5σ₀⁻²σ²T⁻¹}` with `α*` of
Proposition 5.4, let `(mᵢ)` be a solution of (5.10) and `π*` be given by (5.12). Then `π*` is an
equilibrium strategy (Definition 2.1 with the class `Π` of Definition 5.1). -/
theorem theorem_5_5_equilibrium (M : Model) (a : ℝ) (ha : IsAlphaStar M a)
    (hα : max a (1 - 1 / 2 * (M.σ ^ 2 / (M.σ₀ ^ 2 * M.T))) < M.α) (c : Coeffs)
    (hc : SolvesODE510 M c) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) :
    IsEquilibrium M P W (piStar M c) := by sorry

end SmoothAmbEq.Gaussian
