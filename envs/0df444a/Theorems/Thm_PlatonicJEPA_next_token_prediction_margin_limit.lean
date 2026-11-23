-- Prove2me | Theorems.Thm_PlatonicJEPA_next_token_prediction_margin_limit
-- name    : PlatonicJEPA.next_token_prediction_margin_limit
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T12:27:52.62368+00:00
-- url     : https://prove2.me/theorems/cf86b17c-4665-4a4f-a1a8-61360eaf1c60
-- title:
--   Proposition 4 (ii): the temperature-scaled next-token loss tends to the margin
-- statement:
--   Let a context be embedded by $h\in\mathbb{R}^k$, let tokens $v$ in a finite nonempty vocabulary have vectors $w_v$, and let $A(h)=\log\sum_ve^{\langle h,w_v\rangle}$. Then $A$ does not depend on the target token $y$, and $tA(h/t)\to\max_v\langle h,w_v\rangle$ as $t\to0^+$. So the temperature-scaled loss $t\big(-\langle h/t,w_y\rangle+A(h/t)\big)$ tends to the margin
--
--   $$\max_v\langle h,w_v\rangle-\langle h,w_y\rangle\ge0,$$
--
--   which vanishes if and only if the target attains the maximal logit.
-- source:
--   Balestriero and LeCun, Proving and Improving the Platonic Representation Hypothesis with JEPAs, arXiv:2610.39302v1 (2026), Section 2.3, Proposition 4 (ii), eq. (6), p. 6

import Mathlib
import Definitions.Def_PlatonicJEPA_Basic

open MeasureTheory Filter Topology

namespace PlatonicJEPA

theorem next_token_prediction_margin_limit {V : Type*} [Fintype V] [Nonempty V] {k : ℕ}
    (w : V → Fin k → ℝ) (h : Fin k → ℝ) (y : V) :
    Tendsto (fun t : ℝ => t * ntpAntiCollapse w (fun i => h i / t)) (𝓝[>] 0)
      (𝓝 (⨆ v, ∑ i, h i * w v i)) ∧
    Tendsto (fun t : ℝ => t * ntpLoss w (fun i => h i / t) y) (𝓝[>] 0)
      (𝓝 ((⨆ v, ∑ i, h i * w v i) - ∑ i, h i * w y i)) ∧
    0 ≤ (⨆ v, ∑ i, h i * w v i) - ∑ i, h i * w y i ∧
    ((⨆ v, ∑ i, h i * w v i) - ∑ i, h i * w y i = 0 ↔ ∀ v, ∑ i, h i * w v i ≤ ∑ i, h i * w y i) := by sorry

end PlatonicJEPA
