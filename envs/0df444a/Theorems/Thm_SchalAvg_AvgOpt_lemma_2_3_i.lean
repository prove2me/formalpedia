-- Prove2me | Theorems.Thm_SchalAvg_AvgOpt_lemma_2_3_i
-- name    : SchalAvg.AvgOpt.lemma_2_3_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:50:55.068975+00:00
-- url     : https://prove2.me/theorems/e14341e3-495c-45aa-ac43-ca61c2f100d6
-- title:
--   Lemma 2.3(i) — Fatou's lemma for setwise converging probability measures
-- statement:
--   Let $X$ be an arbitrary measurable space, and let $\mu_n$, $\mu$ be probability measures on $X$ with $\mu_n \to \mu$ **setwise**, i.e. $\mu_n(B) \to \mu(B)$ for every measurable set $B$. Let $w_n$ be measurable nonnegative functions on $X$ and $\underline w = \liminf_{n \to \infty} w_n$ (pointwise). Then
--   $$\int \underline w \, d\mu \ \le\ \liminf_{n \to \infty} \int w_n \, d\mu_n.$$
--
--   This version of Fatou's lemma, with the measure varying along the sequence, is what passes the relative discounted optimality equation to the limit under Condition (S).
--
--   **Formalization Note.** The functions take values in $[0, \infty]$ (nonnegative extended reals), which contains the paper's case of finite nonnegative functions; the integrals are lower Lebesgue integrals.
-- source:
--   Schäl, Average Optimality in Dynamic Programming with General State Space, Math. Oper. Res. 18(1) (1993), p. 166, Lemma 2.3(i)

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergLiang.ACOE

namespace SchalAvg.AvgOpt

theorem lemma_2_3_i {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (μs : ℕ → Measure X) [∀ n, IsProbabilityMeasure (μs n)]
    (hμ : ∀ B : Set X, MeasurableSet B → Tendsto (fun n => μs n B) atTop (𝓝 (μ B)))
    (w : ℕ → X → ℝ≥0∞) (hw : ∀ n, Measurable (w n)) :
    ∫⁻ x, liminf (fun n => w n x) atTop ∂μ ≤
      liminf (fun n => ∫⁻ x, w n x ∂(μs n)) atTop := by sorry

end SchalAvg.AvgOpt
