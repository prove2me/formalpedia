-- Prove2me | Theorems.Thm_QuickestOU_Detection_crossing_measure_change
-- name    : QuickestOU.Detection.crossing_measure_change
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-31T18:44:02.559404+00:00
-- url     : https://prove2.me/theorems/166440df-fa52-42b0-ac56-6bc349bbb821
-- title:
--   (4.6) applied to the first-crossing rule (9.12) — risk of the odds-crossing time
-- statement:
--   Let $\pi\in[0,1)$, let $x\in\mathbb R$, and let $X$ be the observed Ornstein–Uhlenbeck process of the disorder model (3.1)–(3.3) (levels zero, $\sigma=1$), whose mean-reversion rate changes from $\beta_0$ to $\beta_1$ at an independent time $\theta$ with $\mathsf P(\theta=0)=\pi$ and $\mathsf P(\theta>t\mid\theta>0)=e^{-\lambda t}$. Let $a:\mathbb R\to\mathbb R$ be any boundary in the class of Theorem 11 (continuous, decreasing on $(-\infty,0]$, increasing on $[0,\infty)$, $a\ge\lambda/c$), and let
--
--   $$\tau_a=\inf\{t\ge0:\ \Phi_t\ge a(X_t)\},$$
--
--   where $\Phi_t$ is the posterior-odds functional (3.12)/(9.12) of the observed path, started at $\Phi_0=\pi/(1-\pi)$.
--
--   Then $\tau_a$ is a stopping time of the natural filtration of $X$, and its Bayes risk (3.4) satisfies the measure-change identity of Proposition 2 in [20] (equations (4.6)–(4.7)):
--
--   $$\mathsf P_\pi(\tau_a<\theta)+c\,\mathsf E_\pi(\tau_a-\theta)^+=(1-\pi)\Big[1+c\,\mathsf E^\infty_{\pi/(1-\pi),x}\Big(\int_0^{\tau_a}e^{-\lambda t}\big(\Phi_t-\tfrac{\lambda}{c}\big)\,dt\Big)\Big],$$
--
--   where on the right the same first-crossing rule is applied to the pair $(\Phi,X)$ driven by the no-change OU flow under $\mathsf P^\infty$ (on any probability space carrying a standard Brownian motion). The identity is stated in the extended reals: both sides may be $+\infty$.
--
--   This is the step "(9.12) follows from (9.7) combined with (3.12) and (4.5)" in the proof of Corollary 12: it transfers the optimality of $\tau_b$ in the no-change problem (4.8) to the original detection problem (3.4).
--
--   **Formalization Note** The disorder model and the no-change model may live on different probability spaces; the rule is the same path functional on both. Risk is in $[0,\infty]$; the right side uses the platform's signed payoff (positive part minus the bounded negative part).
-- source:
--   Glover & Peskir, Quickest detection problems for Ornstein–Uhlenbeck processes, Math. Oper. Res. 49(2) (2024) 1045–1064, https://doi.org/10.1287/moor.2021.0186; Research Report version pp. 8–9 (4.1), (4.6)–(4.7) [Proposition 2 of ref. [20]], p. 7 (3.12), and pp. 26–27, proof of Corollary 12 ((9.12) from (9.7), (3.12), (4.5))

import Mathlib
import Definitions.Def_QuickestOU_Detection_Disorder

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuickestOU.Detection

/-- Proposition 2 of [20] as used in (4.6), applied to the first-crossing rule (9.12):
the first time the pathwise odds of X reach `a(X_t)` is a stopping time of X, and its
Bayes risk equals `(1-π)[1 + c E∞(∫₀^τ e^{-λt}(Φ_t - λ/c) dt)]` for the same rule
applied to the no-change OU flow. -/
theorem crossing_measure_change (P : Params) (hS : P.Standing) (x p0 : ℝ)
    (hp0 : 0 ≤ p0) (hp1 : p0 < 1) (M : DisorderModel P p0 x)
    {Ω' : Type*} [MeasurableSpace Ω'] (μ' : Measure Ω')
    (B' : ℝ≥0 → Ω' → ℝ) (hB' : Driver μ' B')
    (a : ℝ → ℝ) (ha : BoundaryClass P a) :
    IsStoppingTime (natX M) (tauStar M a) ∧
    (risk M (tauStar M a) : EReal) = ((1 - p0 : ℝ) : EReal) *
      (1 + (P.c : EReal) * payoff P B' μ' (p0 / (1 - p0)) x
        (tauB P B' a (p0 / (1 - p0)) x)) := by sorry

end QuickestOU.Detection
