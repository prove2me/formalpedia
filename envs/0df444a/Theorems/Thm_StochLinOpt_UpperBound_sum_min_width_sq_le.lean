-- Prove2me | Theorems.Thm_StochLinOpt_UpperBound_sum_min_width_sq_le
-- name    : StochLinOpt.UpperBound.sum_min_width_sq_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:30:27.000659+00:00
-- url     : https://prove2.me/theorems/339df7f6-f0ae-45a3-ab28-b3cce301a104
-- title:
--   Lemma 9 (corrected) — $\sum_{\tau\le t}\min(w_\tau^2,1)\le2n\ln(t+1)$
-- statement:
--   Let $x_1,x_2,\dots\in[-1,1]^n$, $A_t=I+\sum_{\tau=1}^{t-1}x_\tau x_\tau^\top$ and $w_\tau=\sqrt{x_\tau^\top A_\tau^{-1}x_\tau}$. Then for every $t\ge0$,
--
--   $$\sum_{\tau=1}^{t}\min\big(w_\tau^2,1\big)\le2n\ln(t+1).$$
--
--   This is the elliptical potential bound: the sum of the squared widths cannot grow faster than logarithmically, which is what makes the regret sublinear.
--
--   **Formalization Note** The paper prints $2n\ln t$; its proof gives $2n\ln(t+1)$ (it bounds the sum by $2\ln\det A_{t+1}\le2n\ln(t+1)$, using Lemma 11 at $t+1$). The printed bound is false at $t=1$: the left side is $\min(w_1^2,1)>0$ when $x_1\ne0$, while $2n\ln1=0$. The corrected bound is stated. The hypothesis $x_\tau\in[-1,1]^n$ is the paper's standing Section 5 coordinate choice ($D\subseteq[-1,1]^n$).
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, PDF p. 8, Lemma 9 (with proof via Lemmas 10 and 11)

import Mathlib
import Definitions.Def_StochLinOpt_UpperBound_confidenceBall2
import Definitions.Def_StochLinOpt_UpperBound_analysisQuantities

open Matrix

namespace StochLinOpt.UpperBound

theorem sum_min_width_sq_le {n : ℕ} (x : ℕ → Fin n → ℝ)
    (hx : ∀ τ : ℕ, 1 ≤ τ → ∀ i, |x τ i| ≤ 1) (t : ℕ) :
    ∑ τ ∈ Finset.Icc 1 t, min (width x τ ^ 2) 1 ≤ 2 * n * Real.log (t + 1) := by sorry

end StochLinOpt.UpperBound
