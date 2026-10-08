-- Prove2me | Theorems.Thm_TalagrandConc_OnePoint_remark_2_1_3
-- name    : TalagrandConc.OnePoint.remark_2_1_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:40:11.039636+00:00
-- url     : https://prove2.me/theorems/379ee532-b252-4e02-852c-a38c8bd7a73a
-- title:
--   Remark 2.1.3 — weighted Hamming distance: $\int e^{tf}dP\le e^{t^2\sum a_i^2/4}/P(A)$
-- statement:
--   Let $(\Omega,\Sigma,\mu)$ be a probability space, $P=\mu^N$ on $\Omega^N$, and let $(a_i)_{i\le N}$ be positive numbers. For a measurable $A\subseteq\Omega^N$ let
--   $$f(A,x)=\inf\Big\{\sum\{a_i:\ i\le N,\ x_i\neq y_i\}\ :\ y\in A\Big\}$$
--   be the weighted Hamming distance, and assume $x\mapsto f(A,x)$ is measurable. Then for every $t>0$,
--   $$\int e^{t f(A,x)}\,dP(x)\ \le\ \frac{1}{P(A)}\,e^{t^2\sum_{i\le N}a_i^2/4},$$
--   and for every $u\ge0$,
--   $$P\big(\{f(A,\cdot)\ge u\}\big)\ \le\ \frac{1}{P(A)}\,e^{-u^2/\sum_{i\le N}a_i^2}.$$
--
--   The weighted version is the form used when coordinates contribute unequally, and it is the model for the extensions that the paper leaves unstated in Chapters 2–5.
--
--   **Formalization Note** Same measurability convention as Proposition 2.1.1; the distance lives in $[0,\infty]$, equal to $+\infty$ when $A=\emptyset$. The range $t>0$ is that of Proposition 2.1.1, whose proof the remark invokes.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 84, Remark 2.1.3, Eqs. (2.1.7)–(2.1.9)

import Mathlib
import Definitions.Def_TalagrandConc_OnePoint_Basic

open MeasureTheory
open scoped ENNReal

namespace TalagrandConc.OnePoint

theorem remark_2_1_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (a : Fin N → ℝ) (ha : ∀ i, 0 < a i) (A : Set (Fin N → Ω)) (hA : MeasurableSet A)
    (hf : Measurable (weightedHammingDistToSet a A)) :
    (∀ t : ℝ, 0 < t →
      (∫⁻ x, expMul t (weightedHammingDistToSet a A x) ∂(Measure.pi fun _ : Fin N => μ))
          ≤ ENNReal.ofReal (Real.exp (t ^ 2 * (∑ i, a i ^ 2) / 4))
              / (Measure.pi fun _ : Fin N => μ) A) ∧
    (∀ u : ℝ, 0 ≤ u →
      (Measure.pi fun _ : Fin N => μ) {x | ENNReal.ofReal u ≤ weightedHammingDistToSet a A x}
          ≤ ENNReal.ofReal (Real.exp (-u ^ 2 / ∑ i, a i ^ 2))
              / (Measure.pi fun _ : Fin N => μ) A) := by sorry

end TalagrandConc.OnePoint
