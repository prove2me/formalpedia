-- Prove2me | Theorems.Thm_SKHessianAscent_theorem_3_11
-- name    : SKHessianAscent.theorem_3_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:07:33.17781+00:00
-- url     : https://prove2.me/theorems/189faaf3-2968-4681-8c1e-f9a890ba1ca6
-- title:
--   Theorem 3.11 — a $T_1$ transportation inequality implies sub-Gaussian concentration of Lipschitz functions (Bobkov–Götze)
-- statement:
--   Let $P$ be a probability measure on a metric space that satisfies the $T_1$ transportation inequality with constant $C>0$ (Definition 3.10). Then every $P$-integrable $K_F$-Lipschitz function $F$ satisfies
--   $$\mathbf E_P\big[e^{\lambda(F-\mathbf E_P[F])}\big]\le e^{\lambda^2CK_F^2/2}\quad(\forall\lambda\in\mathbb R),\qquad P\{|F-\mathbf E_P[F]|>r\}\le2e^{-r^2/(2CK_F^2)}\quad(\forall r>0).$$
--
--   **Formalization Note** The exponential moment is a Lebesgue integral with values in $[0,\infty]$, so its finiteness is part of the conclusion.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, §3.4, Theorem 3.11, p. 15 (from Djellout–Guillin–Wu, Theorem 1.1, and Bobkov–Götze)

import Mathlib
import Definitions.Def_SKHessianAscent_Transport

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SKHessianAscent

theorem theorem_3_11 {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E] [BorelSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (C : ℝ) (hC : 0 < C) (hT1 : SatisfiesT 1 C P)
    (F : E → ℝ) (K : ℝ≥0) (hF : LipschitzWith K F) (hint : Integrable F P) :
    (∀ lam : ℝ,
      ∫⁻ x, ENNReal.ofReal (Real.exp (lam * (F x - ∫ y, F y ∂P))) ∂P ≤
        ENNReal.ofReal (Real.exp (lam ^ 2 * C * (K : ℝ) ^ 2 / 2))) ∧
    (∀ r : ℝ, 0 < r →
      P {x | r < |F x - ∫ y, F y ∂P|} ≤
        ENNReal.ofReal (2 * Real.exp (-r ^ 2 / (2 * C * (K : ℝ) ^ 2)))) := by sorry

end SKHessianAscent
