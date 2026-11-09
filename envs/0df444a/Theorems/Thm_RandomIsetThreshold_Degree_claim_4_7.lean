-- Prove2me | Theorems.Thm_RandomIsetThreshold_Degree_claim_4_7
-- name    : RandomIsetThreshold.Degree.claim_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:05:45.319602+00:00
-- url     : https://prove2.me/theorems/3b431413-01ff-418e-a5b4-fa015e7b2277
-- title:
--   Claim 4.7 — uniform lower estimates for the scale
-- statement:
--   For every $r\ge2$ and $\varepsilon>0$, there are $d_0\ge e$, $\xi_0>0$, and an integer $n_0>0$, depending only on $r,\varepsilon$, such that whenever $d\ge d_0$, $0<\xi\le\xi_0$, $n\ge n_0$, and $d/n^{r-1}\le p\le1-n^{-\xi}$,
--
--   $$\min\{L,\varepsilon L\}\ge\frac{4er}{p^{1/(r-1)}}.$$
--
--   Both terms of the minimum are retained. The estimate controls scale and rounding issues in both the impossibility argument and the independence-number estimate.
--
--   Differences from the source:
--   - encoding: vertices [n], all unordered r-sets, and real edge probabilities → Fin n, the subtype of r-element finsets, and unitInterval parameters; reason: order-preserving relabeling; interior biases are imposed or follow from the source regime
--   - encoding: constants with specified parameter dependencies → nested existential witnesses before the parameters on which they may not depend; reason: makes the source uniformity explicit without changing an instance
--   - generalization: 0 < ε ≤ 1, the Section 4 reduction → every ε > 0; reason: the proof on p. 17 bounds the scale by (4er/min{1,ε})^{r-1}, which covers ε > 1 without change, and the range ε ≤ 1 used by Section 4 and by (77) specializes it
-- source:
--   Matthew Cho, Lutz Warnke, STOC 2027 submission #260 (October 2026), p. 17, Claim 4.7

import Mathlib
import Definitions.Def_RandomIsetThreshold_Degree_Hypergraph

open MeasureTheory
open scoped ENNReal BigOperators
universe u_claim_4_7

namespace RandomIsetThreshold.Degree

theorem claim_4_7
(r : ℕ) (hr : 2 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ d₀ : ℝ, Real.exp 1 ≤ d₀ ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧
      ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (d ξ : ℝ), d₀ ≤ d → 0 < ξ → ξ ≤ ξ₀ →
      ∀ n : ℕ, n₀ ≤ n → ∀ p : unitInterval, Regime n r p d ξ →
        4 * Real.exp 1 * (r : ℝ) / Real.rpow (p : ℝ) (1 / ((r : ℝ) - 1)) ≤
          min (scale n r p) (ε * scale n r p) := by sorry

end RandomIsetThreshold.Degree
