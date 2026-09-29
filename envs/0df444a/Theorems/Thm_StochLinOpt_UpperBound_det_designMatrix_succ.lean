-- Prove2me | Theorems.Thm_StochLinOpt_UpperBound_det_designMatrix_succ
-- name    : StochLinOpt.UpperBound.det_designMatrix_succ
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:29:44.816052+00:00
-- url     : https://prove2.me/theorems/e4eee0b6-573d-4e3a-8387-24f409018e0c
-- title:
--   Lemma 10 — $\det A_{t+1}=\prod_{\tau=1}^{t}(1+w_\tau^2)$
-- statement:
--   Let $x_1,x_2,\dots\in\mathbb R^n$ be any sequence, $A_t=I+\sum_{\tau=1}^{t-1}x_\tau x_\tau^\top$ and $w_\tau=\sqrt{x_\tau^\top A_\tau^{-1}x_\tau}$. Then for every $t\ge0$,
--
--   $$\det A_{t+1}=\prod_{\tau=1}^{t}\big(1+w_\tau^2\big).$$
--
--   This expresses the growth of the log-volume of the precision matrix $A_t$ through the widths of the chosen decisions; it is the first half of the potential argument behind Lemma 9.
--
--   **Formalization Note** The paper prints the factor as $(1+w_t^2)$ under $\prod_{\tau=1}^t$; the index is a typo and the proof gives $(1+w_\tau^2)$, which is what is stated. The paper's "for every $t\le T$" places no restriction, so the statement is for every $t$, including $t=0$ (empty product, $A_1=I$).
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, PDF p. 8, Lemma 10

import Mathlib
import Definitions.Def_StochLinOpt_UpperBound_confidenceBall2
import Definitions.Def_StochLinOpt_UpperBound_analysisQuantities

open Matrix

namespace StochLinOpt.UpperBound

theorem det_designMatrix_succ {n : ℕ} (x : ℕ → Fin n → ℝ) (t : ℕ) :
    (designMatrix x (t + 1)).det = ∏ τ ∈ Finset.Icc 1 t, (1 + width x τ ^ 2) := by sorry

end StochLinOpt.UpperBound
