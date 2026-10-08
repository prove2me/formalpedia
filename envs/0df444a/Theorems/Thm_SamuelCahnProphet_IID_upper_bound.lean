-- Prove2me | Theorems.Thm_SamuelCahnProphet_IID_upper_bound
-- name    : SamuelCahnProphet.IID.upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:21:28.097731+00:00
-- url     : https://prove2.me/theorems/9929f18d-f037-4b58-9e4a-46af0d5bfc31
-- title:
--   Proof of Theorem 2, p. 1215 — "because of Theorem 1": EX*ₙ ≤ 2 sup_{t∈T*ₙ} E⁺X_t for i.i.d. Xᵢ ≥ 0
-- statement:
--   Let $n \ge 1$ and let $X_1, \dots, X_n$ be i.i.d. nonnegative random variables with common law $\mu$, a probability measure on $[0, \infty)$. Let $T_n^*$ be the class of threshold rules $t(c)$, $s(c)$ with $c \ge 0$. Then
--   $$
--   EX_n^* \le 2 \sup_{t \in T_n^*} E^+X_t .
--   $$
--
--   This is the upper half of Theorem 2, which the proof attributes to Theorem 1 (p. 1214). It is the i.i.d. case of the goal of the companion mission I of this series.
--
--   **Formalization Note.** The i.i.d. variables are the coordinates of $\mathbb R^n$ under the product measure $\mu^{\otimes n}$, the standard model of an i.i.d. sample; every quantity involved depends only on the joint law. "Nonnegative" is $\mu((-\infty, 0)) = 0$. Expectations are in $[0, \infty]$, so the bound also covers $EX_n^* = \infty$.
-- source:
--   Samuel-Cahn, Comparison of threshold stop rules and maximum for independent nonnegative random variables, Ann. Probab. 12 (1984), p. 1215, proof of Theorem 2, first sentence ("Because of Theorem 1"); Theorem 1, p. 1214

import Mathlib
import Definitions.Def_SamuelCahnProphet_IID_Setting

open MeasureTheory Filter Topology

namespace SamuelCahnProphet.IID

theorem upper_bound (n : ℕ) [NeZero n] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) :
    Emax μ n ≤ 2 * supEplus μ n := by sorry

end SamuelCahnProphet.IID
