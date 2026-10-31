-- Prove2me | Theorems.Thm_PlugInRisk_lemma_4_3
-- name    : PlugInRisk.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:26:26.760992+00:00
-- url     : https://prove2.me/theorems/8171b8d6-cdf4-42cf-bd12-6ffc8834b696
-- title:
--   Lemma 4.3: $|\mathrm{AVaR}_u(X)|\le\|X\|_{L^p}/(1-u)^{1/p}$
-- statement:
--   For every $p\in(1,\infty]$ and every $X\in L^p$,
--
--   $$
--   |\mathrm{AVaR}_u(X)|\le\frac{\|X\|_{L^p}}{(1-u)^{1/p}}\qquad\text{for every }u\in[0,1),
--   $$
--
--   with the convention $1/\infty=0$.
--
--   Differences from the source:
--
--   - generalization: the assumptions of Theorem 4.1 → dropped; reason: the conclusion involves only p, X and u; the lemma itself quantifies p ∈ (1, ∞]
--   - encoding: X ∈ Lᵖ on a probability space → a probability law ν on ℝ with MemLp id p ν, ‖X‖_{Lᵖ} = ‖id‖_{Lᵖ(ν)}; reason: AVaR and the norm depend only on the law
--   - encoding: 1/p with 1/∞ := 0 → (p⁻¹).toReal; reason: same values
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, Lemma 4.3, p.18

import Mathlib
import Definitions.Def_PlugInRisk_avar

open MeasureTheory
open scoped ENNReal

namespace PlugInRisk

/-- **Lemma 4.3** (Bartl & Tangpi, arXiv:2003.10479v2, Lemma 4.3, p.18): "For every p ∈ (1, ∞]
and X ∈ Lᵖ we have that |AVaR_u(X)| ≤ ‖X‖_{Lᵖ} / (1 − u)^{1/p} for every u ∈ [0, 1)."

**Formalization Note** Stated for the law `ν` of `X`: `X ∈ Lᵖ` is `MemLp id p ν` and
`‖X‖_{Lᵖ} = ‖id‖_{Lᵖ(ν)}`. The exponent `1/p` is `(p⁻¹).toReal`, which is `0` at `p = ∞`
(the paper's convention `1/∞ := 0`, p.11). -/
theorem lemma_4_3 (p : ℝ≥0∞) (hp : 1 < p) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : MemLp id p ν) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    |avar ν u| ≤ (eLpNorm id p ν).toReal / (1 - u) ^ (p⁻¹).toReal := by sorry

end PlugInRisk
