-- Prove2me | Theorems.Thm_QuickestOU_Detection_theorem_11
-- name    : QuickestOU.Detection.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:32.132198+00:00
-- url     : https://prove2.me/theorems/0d96bc1d-5a3c-4e80-8da0-710ab810b6b2
-- title:
--   Theorem 11 — unique nonlinear integral equation, value and stopping rule
-- statement:
--   Let $b(x)=\inf\{\varphi\ge0:\widehat V(\varphi,x)=0\}$. Among continuous real functions that decrease on $(-\infty,0]$, increase on $[0,\infty)$, and satisfy $a(x)\ge\lambda/c$, $b$ is the unique solution of the expectation form of (9.5):
--
--   $$\int_0^\infty e^{-\lambda t}\mathsf E^\infty_{b(x),x}\!\left[(\Phi_t-\lambda/c)\mathbf1_{\{\Phi_t<b(X_t)\}}\right]dt=0\qquad(x\in\mathbb R).$$
--
--   For every $\varphi\ge0$ and $x$, the analogous integral with initial odds $\varphi$ equals $\widehat V(\varphi,x)$. The first time $\Phi_t\ge b(X_t)$ is a stopping time attaining this value. These are the three assertions of Theorem 11: boundary characterization, value representation, and optimal rule.
--
--   **Formalization Note** Equation (9.4) identifies this expectation with the paper's transition-density triple integral. Positive and negative parts are separated; finiteness of the positive part is asserted for the value representation.
-- source:
--   Glover & Peskir, Quickest detection problems for Ornstein–Uhlenbeck processes, Research Report No. 11 (2017, revised), Probab. Statist. Group Manchester; to appear in Math. Oper. Res.; https://doi.org/10.1287/moor.2021.0186; p. 24, Theorem 11 (9.5)–(9.7)

import Mathlib
import Definitions.Def_QuickestOU_Detection_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuickestOU.Detection

/-- Theorem 11: existence and uniqueness for (9.5), value representation (9.6), and rule (9.7). -/
theorem theorem_11 (P : Params) (hS : P.Standing)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (hB : Driver μ B) :
    let b := bnd P B μ hB.meas
    BoundaryClass P b ∧ SolvesIE P B μ b ∧
    (∀ a : ℝ → ℝ, BoundaryClass P a → SolvesIE P B μ a → a = b) ∧
    (∀ phi x : ℝ, 0 ≤ phi →
      iePos P B μ b phi x ≠ ⊤ ∧
      VhatR P B μ hB.meas phi x = Vrep P B μ b phi x) ∧
    (∀ phi x : ℝ, 0 ≤ phi →
      IsStoppingTime (natB B hB.meas) (tauB P B b phi x) ∧
      payoff P B μ phi x (tauB P B b phi x) = Vhat P B μ hB.meas phi x)
    := by sorry

end QuickestOU.Detection
