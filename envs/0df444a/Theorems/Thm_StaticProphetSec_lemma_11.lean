-- Prove2me | Theorems.Thm_StaticProphetSec_lemma_11
-- name    : StaticProphetSec.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:19.848794+00:00
-- url     : https://prove2.me/theorems/cfa9a56f-4b47-4d93-8906-29906670caff
-- title:
--   Lemma 11 — $\mathcal{ST}\ge t\cdot k\cdot\mathbb E[\mathrm{UT}_k(D)]+U(t,F)\,\mathbb E[\mathrm{AR}_k(D)]$
-- statement:
--   For all $k\ge1$, $t\ge0$, $p\in[0,1]$ and every instance $F$, the performance of the policy $(t,p)$ satisfies
--
--   $$\mathcal{ST}^t_k(F)\ge t\cdot k\cdot\mathbb E[\mathrm{UT}_k(D)]+U(t,F)\,\mathbb E[\mathrm{AR}_k(D)].$$
--
--   Together with Lemma 10 this gives Lemma 1.
--
--   Differences from the source:
--
--   - generalization: threshold $t$ and $D^t(V)$ → policy $(t,p)$ with tie-breaking coins and $D$ counting eligible applicants; reason: Remark 1, p.5, says all results apply to it; $p=0$ recovers the plain threshold
--   - generalization: values with finite expectations are the implicit reading of ratios → expectations in $[0,\infty]$ with no integrability assumption; reason: the source assumes none; every finite instance is covered
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, Lemma 11, p.33

import Mathlib
import Definitions.Def_StaticProphetSec_performance
import Definitions.Def_StaticProphetSec_expUtil
import Definitions.Def_StaticProphetSec_expAR
import Definitions.Def_StaticProphetSec_U

open MeasureTheory
open scoped ENNReal

namespace StaticProphetSec

/-- Lemma 11 (Arnosti & Ma, arXiv:2108.12893v2, Lemma 11, p.33), for the policy `(t, p)`
(Remark 1, p.5): `ST ≥ t · k · E[UT_k(D)] + U(t, F) · E[AR_k(D)]`. -/
theorem lemma_11 {n : ℕ} (k : ℕ) (hk : 1 ≤ k) (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, μ i (Set.Iio 0) = 0)
    (t p : ℝ) (ht : 0 ≤ t) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ENNReal.ofReal t * (k : ℝ≥0∞) * expUtil k μ t p + U t μ * expAR k μ t p
      ≤ performance k μ t p := by sorry

end StaticProphetSec
