-- Prove2me | Theorems.Thm_TalagrandConc_OnePoint_cor_2_2_3
-- name    : TalagrandConc.OnePoint.cor_2_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:41:50.348161+00:00
-- url     : https://prove2.me/theorems/6dbb0cbd-0dec-4a38-aa40-031f2f1b000a
-- title:
--   Corollary 2.2.3 — $\int e^{tf(A,x)}dP\le P(A)^{-\alpha}\exp N\frac{t^2}{8}(1+\frac1\alpha)$ and the Gaussian tail (2.2.7)
-- statement:
--   Let $(\Omega,\Sigma,\mu)$ be a probability space, $N\ge0$, $P=\mu^N$ the product probability on $\Omega^N$, and let $A\subseteq\Omega^N$ be measurable. Let
--   $$f(A,x)=\min\big\{\operatorname{card}\{i\le N:\ x_i\ne y_i\}:\ y\in A\big\}$$
--   be the Hamming distance from $x$ to $A$, and assume $x\mapsto f(A,x)$ is measurable. Then:
--
--   1. for every $\alpha>0$ and every $t\ge0$,
--   $$\int e^{t f(A,x)}\,dP(x)\ \le\ \frac{1}{P(A)^{\alpha}}\exp\Big(N\,\frac{t^2}{8}\Big(1+\frac1\alpha\Big)\Big);$$
--   2. if $P(A)>0$, then for every $k\ge\sqrt{\frac N2\log\frac1{P(A)}}$,
--   $$P\big(\{f(A,\cdot)\ge k\}\big)\ \le\ \exp\Big(-\frac2N\Big(k-\sqrt{\frac N2\log\frac1{P(A)}}\Big)^2\Big).$$
--
--   The tail bound (2.2.7) has the optimal Gaussian constant $2/N$ in the exponent, the same as the best bound obtained by martingale methods, and it holds for an arbitrary probability space $\Omega$ and arbitrary measurable $A$.
--
--   **Formalization Note** The paper treats all sets and functions as measurable; the Lean statement makes this an explicit measurability hypothesis on $f(A,\cdot)$. Distances and integrals are in $[0,\infty]$, $P(A)^{\alpha}$ is computed in $[0,\infty]$ (so $P(A)=0$ gives $+\infty$ on the right of (2.2.6)), and (2.2.7) assumes $P(A)>0$, which the paper's $\log(1/P(A))$ requires. At $N=0$ Lean reads $2/N$ as $0$, which leaves a true statement.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 86, Corollary 2.2.3, Eqs. (2.2.6)–(2.2.7)

import Mathlib
import Definitions.Def_TalagrandConc_OnePoint_Basic

open MeasureTheory
open scoped ENNReal

namespace TalagrandConc.OnePoint

theorem cor_2_2_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (A : Set (Fin N → Ω)) (hA : MeasurableSet A)
    (hf : Measurable (hammingDistToSet A)) :
    (∀ α : ℝ, 0 < α → ∀ t : ℝ, 0 ≤ t →
      (∫⁻ x, expMul t (hammingDistToSet A x) ∂(Measure.pi fun _ : Fin N => μ))
        ≤ ENNReal.ofReal (Real.exp (N * (t ^ 2 / 8) * (1 + 1 / α)))
            / (Measure.pi fun _ : Fin N => μ) A ^ α) ∧
    (0 < (Measure.pi fun _ : Fin N => μ) A → ∀ k : ℝ,
      Real.sqrt (N / 2 * Real.log (1 / ((Measure.pi fun _ : Fin N => μ) A).toReal)) ≤ k →
      (Measure.pi fun _ : Fin N => μ) {x | ENNReal.ofReal k ≤ hammingDistToSet A x}
        ≤ ENNReal.ofReal (Real.exp (-(2 / N) *
            (k - Real.sqrt (N / 2 * Real.log (1 / ((Measure.pi fun _ : Fin N => μ) A).toReal))) ^ 2))) := by sorry

end TalagrandConc.OnePoint
