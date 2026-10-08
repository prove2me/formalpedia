-- Prove2me | Theorems.Thm_TalagrandConc_OnePoint_prop_2_1_1
-- name    : TalagrandConc.OnePoint.prop_2_1_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:39:46.060491+00:00
-- url     : https://prove2.me/theorems/7a897e94-ad2d-48b0-9b40-0d603afa639b
-- title:
--   Proposition 2.1.1 — $\int e^{tf(A,x)}dP\le a(t)^N/P(A)\le e^{t^2N/4}/P(A)$ and $P(f(A,\cdot)\ge k)\le e^{-k^2/N}/P(A)$
-- statement:
--   Let $(\Omega,\Sigma,\mu)$ be a probability space, $N\ge0$, $P=\mu^{N}$ the product probability on $\Omega^N$, and let $A\subseteq\Omega^N$ be measurable. Let $f(A,x)$ be the Hamming distance from $x$ to $A$, and assume $x\mapsto f(A,x)$ is measurable. Then:
--
--   1. for every $t>0$,
--   $$\int e^{t f(A,x)}\,dP(x)\ \le\ \frac{1}{P(A)}\Big(\frac12+\frac{e^t+e^{-t}}{4}\Big)^N\ \le\ \frac{1}{P(A)}\,e^{t^2N/4};$$
--   2. for every $k\ge 0$,
--   $$P\big(\{f(A,\cdot)\ge k\}\big)\ \le\ \frac{1}{P(A)}\,e^{-k^2/N}.$$
--
--   This is the basic concentration principle for product measures: a set of not-too-small measure has most of the space within Hamming distance $O(\sqrt N)$, with a Gaussian tail.
--
--   **Formalization Note** The paper states (2.1.2) with an upper integral and (2.1.3) with an outer probability, then adopts the convention of treating all sets and functions as measurable; the Lean statement makes this convention an explicit measurability hypothesis on $f(A,\cdot)$, and integrates in $[0,\infty]$. When $P(A)=0$ the right-hand sides are $+\infty$. The tail bound is stated for real $k\ge0$ (the paper's choice $t=2k/N$ needs $k>0$; $k=0$ is trivial). At $N=0$ Lean reads $k^2/0$ as $0$, which leaves a true statement.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 82, Proposition 2.1.1, Eqs. (2.1.2)–(2.1.3)

import Mathlib
import Definitions.Def_TalagrandConc_OnePoint_Basic

open MeasureTheory
open scoped ENNReal

namespace TalagrandConc.OnePoint

theorem prop_2_1_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (A : Set (Fin N → Ω)) (hA : MeasurableSet A)
    (hf : Measurable (hammingDistToSet A)) :
    (∀ t : ℝ, 0 < t →
      (∫⁻ x, expMul t (hammingDistToSet A x) ∂(Measure.pi fun _ : Fin N => μ))
          ≤ ENNReal.ofReal (aOne t) ^ N / (Measure.pi fun _ : Fin N => μ) A ∧
      ENNReal.ofReal (aOne t) ^ N / (Measure.pi fun _ : Fin N => μ) A
          ≤ ENNReal.ofReal (Real.exp (t ^ 2 * N / 4)) / (Measure.pi fun _ : Fin N => μ) A) ∧
    (∀ k : ℝ, 0 ≤ k →
      (Measure.pi fun _ : Fin N => μ) {x | ENNReal.ofReal k ≤ hammingDistToSet A x}
          ≤ ENNReal.ofReal (Real.exp (-k ^ 2 / N)) / (Measure.pi fun _ : Fin N => μ) A) := by sorry

end TalagrandConc.OnePoint
