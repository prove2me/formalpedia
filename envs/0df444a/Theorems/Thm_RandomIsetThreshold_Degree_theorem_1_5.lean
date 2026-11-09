-- Prove2me | Theorems.Thm_RandomIsetThreshold_Degree_theorem_1_5
-- name    : RandomIsetThreshold.Degree.theorem_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:11:19.090525+00:00
-- url     : https://prove2.me/theorems/e5a397c9-5db8-4290-89c1-c012c4e82d46
-- title:
--   Theorem 1.5 — impossibility from low noise sensitivity
-- statement:
--   Fix $r\ge2$ and $\varepsilon>0$. There are $d,\gamma>0$ depending only on $r,\varepsilon$. For every $\delta>0$, there are $\xi>0$, an integer $n_0>0$ and $\kappa\in(0,1/e)$ depending only on $r,\varepsilon,\delta$. Uniformly for $n\ge n_0$ and $d/n^{r-1}\le p\le1-n^{-\xi}$, one has $pL^r\ge1$. Every measurable random function $f$ with arbitrary independent seed and
--
--   $$\operatorname{NS}_{\tau_0}(f)\le\kappa L\quad\text{for some }\tau_0\in\left[\frac{\sqrt\kappa}{pL^r},1\right]$$
--
--   satisfies
--
--   $$\Pr\bigl(\exists I\text{ independent in }H_{n,p}:\ |I|\ge(1+\varepsilon)L,\ \|f(H_{n,p},R)-1_I\|_2^2\le\gamma|I|\bigr)\le\delta.$$
--
--   The statement covers all $\varepsilon,\delta>0$ and has no norm or polynomial hypothesis. In particular, constant-in-graph random offsets with infinite norm are not excluded.
--
--   Differences from the source:
--   - encoding: vertices [n], all unordered r-sets, and real edge probabilities → Fin n, the subtype of r-element finsets, and unitInterval parameters; reason: order-preserving relabeling; interior biases are imposed or follow from the source regime
--   - encoding: independent random seeds and nonnegative expectations → an arbitrary measurable probability space, product sampling, seedwise measurability, and ENNReal moments; reason: the standing measurability convention makes probabilities meaningful; infinite moments retain their value
--   - encoding: constants with specified parameter dependencies → nested existential witnesses before the parameters on which they may not depend; reason: makes the source uniformity explicit without changing an instance
--   - encoding: a supremum over all admissible random functions → a bound for every such function on every probability seed space; reason: equivalent upper bound, avoiding a supremum indexed by universes
-- source:
--   Matthew Cho, Lutz Warnke, STOC 2027 submission #260 (October 2026), p. 4, Theorem 1.5, equation (8)

import Mathlib
import Definitions.Def_RandomIsetThreshold_Degree_RandomOutput

open MeasureTheory
open scoped ENNReal BigOperators
universe u_theorem_1_5

namespace RandomIsetThreshold.Degree

theorem theorem_1_5
(r : ℕ) (hr : 2 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ d γ : ℝ, 0 < d ∧ 0 < γ ∧
      ∀ δ : ℝ, 0 < δ → ∃ ξ : ℝ, 0 < ξ ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∃ κ : ℝ, (0 < κ ∧ κ < 1 / Real.exp 1) ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ p : unitInterval, Regime n r p d ξ →
        1 ≤ (p : ℝ) * scale n r p ^ r ∧
        ∀ (Ω : Type u_theorem_1_5) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (f : Cube n r → Ω → Vector n), SeedMeasurable f →
          (∃ τ₀ : unitInterval,
            Real.sqrt κ / ((p : ℝ) * scale n r p ^ r) ≤ (τ₀ : ℝ) ∧
              noiseSensitivity p τ₀ μ f ≤ ENNReal.ofReal (κ * scale n r p)) →
          successProbability p μ f ε γ ≤ δ := by sorry

end RandomIsetThreshold.Degree
