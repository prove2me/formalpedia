-- Prove2me | Theorems.Thm_StaticProphetSec_lemma_1
-- name    : StaticProphetSec.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:38.515994+00:00
-- url     : https://prove2.me/theorems/76cf34c6-753c-453c-91f3-96ee601873ac
-- title:
--   Lemma 1 — $\mathcal{ST}/\mathcal{PHT}\ge\mathcal{ST}/\mathcal{LP}\ge\min(\mathbb E[\mathrm{UT}_k(D)],\mathbb E[\mathrm{AR}_k(D)])$
-- statement:
--   For all $k\ge1$, $t\ge0$, $p\in[0,1]$ and every instance $F$,
--
--   $$\frac{\mathcal{ST}^t_k(F)}{\mathcal{PHT}_k(F)}\ge\frac{\mathcal{ST}^t_k(F)}{\mathcal{LP}_k(F)}\ge\min\big(\mathbb E[\mathrm{UT}_k(D)],\ \mathbb E[\mathrm{AR}_k(D)]\big).$$
--
--   This separates the two risks of a threshold, under-allocation and allocating too quickly.
--
--   Differences from the source:
--
--   - generalization: threshold $t$ and $D^t(V)$ → policy $(t,p)$ with tie-breaking coins and $D$ counting eligible applicants; reason: Remark 1, p.5, says all results apply to it; $p=0$ recovers the plain threshold
--   - generalization: values with finite expectations are the implicit reading of ratios → expectations in $[0,\infty]$ with no integrability assumption; reason: the source assumes none; every finite instance is covered
--   - encoding: ratios $\mathcal{ST}/\mathcal{PHT}\ge\mathcal{ST}/\mathcal{LP}\ge\min(\cdot)$ → $\mathcal{PHT}\le\mathcal{LP}$ and $\min(\cdot)\,\mathcal{LP}\le\mathcal{ST}$; reason: ratios are undefined at a zero denominator; the products are equivalent elsewhere
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, Lemma 1, p.17

import Mathlib
import Definitions.Def_StaticProphetSec_performance
import Definitions.Def_StaticProphetSec_expUtil
import Definitions.Def_StaticProphetSec_expAR
import Definitions.Def_StaticProphetSec_prophet
import Definitions.Def_StaticProphetSec_lpValue

open MeasureTheory
open scoped ENNReal

namespace StaticProphetSec

/-- Lemma 1 (Arnosti & Ma, arXiv:2108.12893v2, Lemma 1, p.17), for the policy `(t, p)` (Remark 1,
p.5): `ST/PHT ≥ ST/LP ≥ min(E[UT_k(D)], E[AR_k(D)])`.

**Formalization Note.** The ratios are written as products, so a zero denominator causes no junk
value: the first inequality is `PHT ≤ LP`, the second `min(…) · LP ≤ ST`. -/
theorem lemma_1 {n : ℕ} (k : ℕ) (hk : 1 ≤ k) (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, μ i (Set.Iio 0) = 0)
    (t p : ℝ) (ht : 0 ≤ t) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    prophet k μ ≤ lpValue k μ ∧
    min (expUtil k μ t p) (expAR k μ t p) * lpValue k μ ≤ performance k μ t p := by sorry

end StaticProphetSec
