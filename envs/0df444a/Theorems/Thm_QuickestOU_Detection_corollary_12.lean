-- Prove2me | Theorems.Thm_QuickestOU_Detection_corollary_12
-- name    : QuickestOU.Detection.corollary_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:24.325044+00:00
-- url     : https://prove2.me/theorems/a8ef9253-5f76-4677-8884-3cdca7a97712
-- title:
--   Corollary 12 — Bayes risk and optimal detection through b
-- statement:
--   In the Ornstein–Uhlenbeck disorder model with prior $\pi\in[0,1]$, initial observation $x$, and rates $\beta_0\ne\beta_1$, let $b$ be the stopping boundary of the no-change value $\widehat V$. The boundary is the unique solution of (9.5) in the paper's continuous, two-sided monotone class with lower bound $\lambda/c$. Writing $\widehat V$ by its (9.6) representation, the original Bayes value is
--
--   $$V(\pi)=(1-\pi)\left[1+c\widehat V\left(\frac{\pi}{1-\pi},x\right)\right].$$
--
--   For $\pi<1$, the first time the pathwise posterior odds $\Phi_t$ of (9.12) reach $b(X_t)$ is a stopping time of the observed process $X$ and attains the infimum defining $V(\pi)$. Here $\Phi_0=\pi/(1-\pi)$, $\delta=\beta_0-\beta_1$, and $\kappa=\beta_0+\beta_1$.
--
--   This is the paper's solution of the initial Bayesian detection problem.
--
--   **Formalization Note** The paper displays $\pi\in[0,1]$ in (9.11) but its stopping formula divides by $1-\pi$. The optimality clause is restricted to $\pi<1$; the value identity includes $\pi=1$. The integral equation is used in its equivalent expectation form (9.4).
-- source:
--   Glover & Peskir, Quickest detection problems for Ornstein–Uhlenbeck processes, Research Report No. 11 (2017, revised), Probab. Statist. Group Manchester; to appear in Math. Oper. Res.; https://doi.org/10.1287/moor.2021.0186; pp. 26–27, Corollary 12 (9.11)–(9.12)

import Mathlib
import Definitions.Def_QuickestOU_Detection_Disorder

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuickestOU.Detection

/-- Corollary 12, (9.11)--(9.12): Bayes risk and optimal detection through the unique boundary. -/
theorem corollary_12 (P : Params) (hS : P.Standing) (x p0 : ℝ)
    (hp0 : 0 ≤ p0) (hp1 : p0 ≤ 1) (M : DisorderModel P p0 x)
    {Ω' : Type*} [MeasurableSpace Ω'] (μ' : Measure Ω')
    (B' : ℝ≥0 → Ω' → ℝ) (hB' : Driver μ' B') :
    let b := bnd P B' μ' hB'.meas
    BoundaryClass P b ∧ SolvesIE P B' μ' b ∧
    (∀ a : ℝ → ℝ, BoundaryClass P a → SolvesIE P B' μ' a → a = b) ∧
    iePos P B' μ' b (p0 / (1 - p0)) x ≠ ⊤ ∧
    (Vpi M).toReal = (1 - p0) *
      (1 + P.c * Vrep P B' μ' b (p0 / (1 - p0)) x) ∧
    (p0 < 1 →
      IsStoppingTime (natX M) (tauStar M b) ∧
      risk M (tauStar M b) = Vpi M)
    := by sorry

end QuickestOU.Detection
