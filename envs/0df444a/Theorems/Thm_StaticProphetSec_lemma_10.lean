-- Prove2me | Theorems.Thm_StaticProphetSec_lemma_10
-- name    : StaticProphetSec.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:13.862463+00:00
-- url     : https://prove2.me/theorems/3b4c1da2-f325-4b03-9d12-8b8f4c75cfd2
-- title:
--   Lemma 10 — $\mathcal{PHT}_k(F)\le\mathcal{LP}_k(F)\le t\cdot k+U(t,F)$
-- statement:
--   For all $k\ge1$, all $t\ge0$ and every instance $F$,
--
--   $$\mathcal{PHT}_k(F)\le\mathcal{LP}_k(F)\le t\cdot k+U(t,F).$$
--
--   The first inequality says that the LP relaxation is a stronger benchmark than the prophet; the second gives the upper bound that Lemma 11 is compared with.
--
--   Differences from the source:
--
--   - generalization: values with finite expectations are the implicit reading of ratios → expectations in $[0,\infty]$ with no integrability assumption; reason: the source assumes none; every finite instance is covered
--   - encoding: $x_i\ge0$ in $\mathcal{LP}_k$ → $0\le x_i\le1$; reason: $F_i^{-1}$ is undefined below $0$ and $x_i$ is a probability, p.16; only undefined cases are excluded
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, Lemma 10, p.32

import Mathlib
import Definitions.Def_StaticProphetSec_prophet
import Definitions.Def_StaticProphetSec_lpValue
import Definitions.Def_StaticProphetSec_U

open MeasureTheory
open scoped ENNReal

namespace StaticProphetSec

/-- Lemma 10 (Arnosti & Ma, arXiv:2108.12893v2, Lemma 10, p.32): for all `k`, `t ≥ 0` and all
`F`, `PHT_k(F) ≤ LP_k(F) ≤ t · k + U(t, F)`. -/
theorem lemma_10 {n : ℕ} (k : ℕ) (hk : 1 ≤ k) (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, μ i (Set.Iio 0) = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    prophet k μ ≤ lpValue k μ ∧ lpValue k μ ≤ ENNReal.ofReal t * (k : ℝ≥0∞) + U t μ := by sorry

end StaticProphetSec
