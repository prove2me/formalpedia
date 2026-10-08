-- Prove2me | Theorems.Thm_SamuelCahnProphet_IID_theorem_2
-- name    : SamuelCahnProphet.IID.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:22:13.368163+00:00
-- url     : https://prove2.me/theorems/9e3c98c4-1de2-4a1b-8a1f-333af6d617f3
-- title:
--   Theorem 2, p. 1215 — for i.i.d. Xᵢ ≥ 0, sup_n sup_X EX*ₙ/sup_{T*ₙ} E⁺X_t = sup_n sup_X EX*ₙ/sup_{T*ₙ} EX_t = 2
-- statement:
--   Let $X_1, \dots, X_n$ be i.i.d. nonnegative random variables, $X_n^* = \max(X_1, \dots, X_n)$, and let $T_n^*$ be the class of threshold rules $t(c)$, $s(c)$ with $c \ge 0$. Theorem 2 of Samuel-Cahn (1984) states
--   $$
--   \sup_n \sup_{\underline X} \left[\frac{EX_n^*}{\sup_{t \in T_n^*} E^+X_t}\right] = \sup_n \sup_{\underline X} \left[\frac{EX_n^*}{\sup_{t \in T_n^*} EX_t}\right] = 2,
--   $$
--   the inner suprema ranging over all i.i.d. nonnegative $\underline X = (X_1, \dots, X_n)$. It is stated here as three facts:
--
--   1. for every $n \ge 1$ and every law $\mu$ on $[0, \infty)$, $EX_n^* \le 2 \sup_{t \in T_n^*} E^+X_t$;
--   2. for every $n \ge 1$ and every law, $\sup_{t \in T_n^*} E^+X_t \le \sup_{t \in T_n^*} EX_t$;
--   3. for every $\varepsilon > 0$ there are $n \ge 1$ and a law $\mu$ on $[0, \infty)$ with $(2 - \varepsilon) \sup_{t \in T_n^*} EX_t < EX_n^*$.
--
--   Facts 1 and 2 bound both ratios by $2$; fact 3 shows that the second ratio exceeds $2 - \varepsilon$, and by fact 2 so does the first. So both suprema equal $2$: the factor $2$ of Theorem 1 cannot be improved for threshold rules, even for i.i.d. variables.
--
--   **Formalization Note.** The i.i.d. variables are the coordinates of $\mathbb R^n$ under the product measure $\mu^{\otimes n}$ (the standard i.i.d. model; all quantities depend only on the joint law), so the supremum over $\underline X$ is a supremum over probability laws $\mu$ with $\mu((-\infty, 0)) = 0$. Expectations are in $[0, \infty]$. The ratios are not written literally, because in $[0, \infty]$ the quotients $0/0$ and $\infty/\infty$ take junk values; the three facts give the page's two equalities wherever the ratios are defined. The strict inequality in fact 3 excludes witnesses with $EX_n^* = 0$ or $\sup_t EX_t = \infty$. In fact 3 the sample size is written $n + 1$ with $n \in \mathbb N$, so that it is at least $1$. Fact 2 holds for every measure and is stated without the probability hypothesis.
-- source:
--   Samuel-Cahn, Comparison of threshold stop rules and maximum for independent nonnegative random variables, Ann. Probab. 12 (1984), p. 1215, Theorem 2

import Mathlib
import Definitions.Def_SamuelCahnProphet_IID_Setting

open MeasureTheory Filter Topology

namespace SamuelCahnProphet.IID

theorem theorem_2 :
    (∀ (n : ℕ) [NeZero n] (μ : Measure ℝ) [IsProbabilityMeasure μ], μ (Set.Iio 0) = 0 →
        Emax μ n ≤ 2 * supEplus μ n) ∧
      (∀ (n : ℕ) [NeZero n] (μ : Measure ℝ), supEplus μ n ≤ supE μ n) ∧
      (∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (μ : Measure ℝ), IsProbabilityMeasure μ ∧ μ (Set.Iio 0) = 0 ∧
        ENNReal.ofReal (2 - ε) * supE μ (n + 1) < Emax μ (n + 1)) := by sorry

end SamuelCahnProphet.IID
