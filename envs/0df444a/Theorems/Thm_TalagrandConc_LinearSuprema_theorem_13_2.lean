-- Prove2me | Theorems.Thm_TalagrandConc_LinearSuprema_theorem_13_2
-- name    : TalagrandConc.LinearSuprema.theorem_13_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:46:51.014979+00:00
-- url     : https://prove2.me/theorems/9d60ff4b-7d3f-4d4a-a488-f0b96bcb4a69
-- title:
--   Theorem 13.2 — concentration of a Banach-space random sum
-- statement:
--   Let $v_1,\ldots,v_N$ lie in a real Banach space $W$. Define
--   $$\sigma=\left(\sup_{w^*\in W^*,\,\|w^*\|\le1}\sum_iw^*(v_i)^2\right)^{1/2},$$
--   and assume $\sigma>0$. Let $Y_i$ be independent real random variables satisfying $|Y_i|\le1$
--   almost surely, and let $M$ be any median of $S=\|\sum_iY_iv_i\|$. For every $t>0$,
--   $$P(|S-M|\ge t\sigma)\le4\exp(-t^2/16).$$
--
--   This specialization gives a dimension-independent tail bound for the norm of a random
--   vector sum.
--
--   **Formalization Note** The positive-scale hypothesis excludes the all-zero-vector case,
--   where the source's displayed inequality with a non-strict tail event is false for large $t$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 198, Theorem 13.2, Eqs. (13.10)–(13.11)

import Mathlib
import Definitions.Def_TalagrandConc_LinearSuprema_Basic
import Definitions.Def_TalagrandConc_LinearSuprema_Banach

namespace TalagrandConc.LinearSuprema

theorem theorem_13_2 {N : ℕ} {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [CompleteSpace W]
    (v : Fin N → W) (hσ : 0 < weakSigma v)
    (μ : Fin N → MeasureTheory.Measure ℝ)
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, μ i (Set.Icc (-1 : ℝ) 1) = 1)
    (M : ℝ)
    (hM : TalagrandConc.BinPacking.IsMedian (MeasureTheory.Measure.pi μ) (vectorSumNorm v) M)
    (t : ℝ) (ht : 0 < t) :
    (MeasureTheory.Measure.pi μ)
        {y | |vectorSumNorm v y - M| ≥ t * weakSigma v} ≤
      ENNReal.ofReal (4 * Real.exp (-(t ^ 2) / 16)) := by sorry

end TalagrandConc.LinearSuprema
