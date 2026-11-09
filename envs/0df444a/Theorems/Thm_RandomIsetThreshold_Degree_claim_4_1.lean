-- Prove2me | Theorems.Thm_RandomIsetThreshold_Degree_claim_4_1
-- name    : RandomIsetThreshold.Degree.claim_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:17:12.97042+00:00
-- url     : https://prove2.me/theorems/6749fe2f-a260-4a12-96b2-27b5ac0c7c15
-- title:
--   Claim 4.1 — small resampling rate
-- statement:
--   Fix $r\ge2$ and $0<\kappa<1/e$. There are $\xi_0>0$ and an integer $n_0>0$, depending only on $r,\kappa$, such that for every $0<\xi\le\xi_0$, $n\ge n_0$ and $e/n^{r-1}\le p\le1-n^{-\xi}$,
--
--   $$\frac{\log(1/\kappa)}{pL^r}\le\frac12.$$
--
--   This supplies a valid resampling rate uniformly over the source bias interval. **Formalization Note** Any source lower bound $d\ge e$ implies the lower bound used here.
--
--   Differences from the source:
--   - encoding: vertices [n], all unordered r-sets, and real edge probabilities → Fin n, the subtype of r-element finsets, and unitInterval parameters; reason: order-preserving relabeling; interior biases are imposed or follow from the source regime
--   - encoding: constants with specified parameter dependencies → nested existential witnesses before the parameters on which they may not depend; reason: makes the source uniformity explicit without changing an instance
--   - encoding: the standing condition d ≥ e and lower bound d/n^{r-1} → the weakest standing lower bound e/n^{r-1}; reason: the claim is uniform for d ≥ e, and its proof (51), (53) uses only log d ≥ 1
-- source:
--   Matthew Cho, Lutz Warnke, STOC 2027 submission #260 (October 2026), p. 14, Claim 4.1; proof (51), (53) on p. 17

import Mathlib
import Definitions.Def_RandomIsetThreshold_Degree_ResamplingPath

open MeasureTheory
open scoped ENNReal BigOperators
universe u_claim_4_1

namespace RandomIsetThreshold.Degree

theorem claim_4_1
(r : ℕ) (hr : 2 ≤ r) (κ : ℝ) (hκ : 0 < κ ∧ κ < 1 / Real.exp 1) :
    ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (ξ : ℝ), 0 < ξ → ξ ≤ ξ₀ → ∀ n : ℕ, n₀ ≤ n →
      ∀ p : unitInterval, Regime n r p (Real.exp 1) ξ →
        noiseRate n r p κ ≤ 1 / 2 := by sorry

end RandomIsetThreshold.Degree
