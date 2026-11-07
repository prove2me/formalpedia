-- Prove2me | Theorems.Thm_PathORAMCap_lemma_4_14
-- name    : PathORAMCap.lemma_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:47:53.137298+00:00
-- url     : https://prove2.me/theorems/9a627cb3-ffa2-4bb1-8aa4-e23faeff66ed
-- title:
--   Lemma 4.14 — categorical Poissonization: $\mathbb E[f(z+V)]\le\mathbb E[f(z+C)]$
-- statement:
--   Let $p_1,\dots,p_d\ge0$ with $\sum_ip_i\le1$. Let $V$ be the $i$-th unit vector $e_i$ with probability $p_i$ and $0$ with probability $1-\sum_ip_i$, and let $C=(C_1,\dots,C_d)$ have independent coordinates $C_i\sim\mathrm{Poisson}(p_i)$. For every increasing directionally convex $f$ on $[0,\infty)^d$ and every deterministic $z\ge0$,
--
--   $$\mathbb E[f(z+V)]\le\mathbb E[f(z+C)].$$
--
--   The same inequality holds for a random background $Y\ge0$ independent of the placements, with $V$ and $C$ each sampled independently of $Y$.
--
--   One placement of a block can therefore be replaced by independent Poisson counts with the same means without decreasing the expected cost; repeated, this gives node loads that are independent given the paths.
--
--   **Formalization Note** The two sides are compared through the increments over the background, $\mathbb E[f(z+V)-f(z)]\le\mathbb E[f(z+C)-f(z)]$, in $[0,\infty]$; when the expectations are finite this is the printed inequality, and $\mathbb E[f(z+C)]$ may be infinite. The background is a probability measure on $\mathbb R^d$ carried by the orthant.
--
--   Differences from the source:
--
--   - encoding: E[f(z + V)] ≤ E[f(z + C)] (and with a random background Y) → E[f(z + V) − f(z)] ≤ E[f(z + C) − f(z)] in ℝ≥0∞ (and the same integrated over the law of Y); reason: the increments are nonnegative since f is increasing; the two forms agree whenever the printed expectations are finite, and the ℝ≥0∞ form is meaningful when E[f(z + C)] = +∞
--   - encoding: a random background independent of the placements → a probability measure μ on ℝ^d with μ-a.e. nonnegative values, integrated against the laws of V and C (product law); reason: the expectations depend only on the joint law, which independence makes the product; backgrounds are loads, nonnegative as the deterministic z ≥ 0
--   - encoding: the expectation over a general random background → Measurable f in the background clause; reason: the expectation over a non-discrete law is defined only for measurable integrands; for deterministic z (discrete V, C) no hypothesis is added
-- source:
--   Chang, Au, The Minimum Bucket Capacity for Reliable Path ORAM, STOC 2027 submission (manuscript sha256 1762f048…), Lemma 4.14, p.23 (PDF p.26); definition (25), p.22 (PDF p.25)

import Mathlib
import Definitions.Def_PathORAMCap_IsIncrDirConvex

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PathORAMCap

/-- **Lemma 4.14** (Categorical Poissonization; Chang, Au, *The Minimum Bucket Capacity for Reliable Path ORAM*, STOC 2027 submission (manuscript sha256 1762f048…), p.23 (PDF p.26)): "Let p1, . . . , pd ≥ 0 with
Σi pi ≤ 1, and let V equal the ith coordinate unit vector with probability pi and zero with
probability 1−Σi pi. Let C = (C1, . . . , Cd) have independent coordinates with Ci ∼ Poisson(pi). For
every increasing directionally convex f and deterministic z ≥ 0, E[f(z + V)] ≤ E[f(z + C)]. The same
inequality holds for a random background independent of the placements, with V and C each sampled
independently of that background."

**Formalization Note.** Expectations are compared through the increments over the background,
`E[f(z + V) − f(z)] ≤ E[f(z + C) − f(z)]`, in `ℝ≥0∞` (nonnegative since `f` is increasing):
`E[f(z + C)]` may be `+∞`, and in `ℝ` the series would need a summability hypothesis. The outcome
`V = 0` contributes the increment `0`. The law of `C` is the product of `poissonMeasure (p i)`. The
random background `Y ≥ 0` is a probability measure `μ` on `ℝ^d`, independent of `V`, `C` (so the
joint law is the product); its clause carries `Measurable f`, which makes the expectation over `μ`
defined. -/
theorem lemma_4_14 (d : ℕ) (p : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i ≤ 1)
    (f : (Fin d → ℝ) → ℝ) (hf : IsIncrDirConvex f) :
    (∀ z : Fin d → ℝ, 0 ≤ z →
      ∑ i, ENNReal.ofReal (p i) * ENNReal.ofReal (f (z + Pi.single i 1) - f z) ≤
        ∑' c : Fin d → ℕ, (∏ i, poissonMeasure (p i).toNNReal {c i}) *
          ENNReal.ofReal (f (z + fun i => (c i : ℝ)) - f z)) ∧
    (Measurable f → ∀ μ : Measure (Fin d → ℝ), IsProbabilityMeasure μ → (∀ᵐ y ∂μ, 0 ≤ y) →
      ∫⁻ y, ∑ i, ENNReal.ofReal (p i) * ENNReal.ofReal (f (y + Pi.single i 1) - f y) ∂μ ≤
        ∫⁻ y, ∑' c : Fin d → ℕ, (∏ i, poissonMeasure (p i).toNNReal {c i}) *
          ENNReal.ofReal (f (y + fun i => (c i : ℝ)) - f y) ∂μ) := by sorry

end PathORAMCap
