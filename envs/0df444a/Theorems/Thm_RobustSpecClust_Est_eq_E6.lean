-- Prove2me | Theorems.Thm_RobustSpecClust_Est_eq_E6
-- name    : RobustSpecClust.Est.eq_E6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:34.869983+00:00
-- url     : https://prove2.me/theorems/9cf62c97-88a0-400c-ad69-76ac2bd775bb
-- title:
--   (E.6), p. 40 — Hsu–Kakade–Zhang: P(‖x‖² > s²(d + 2√(td) + 2t)) ≤ e^{−t} for sub-gaussian x
-- statement:
--   Let $x$ be a random vector in $\mathbb R^d$ that is sub-gaussian with parameter $s$ in the sense of Definition 3 (mean zero, $\mathbb E[e^{\nu^\top x}] \le e^{s^2\|\nu\|^2/2}$ for all $\nu$). Then for every $t > 0$,
--   $$\mathbb P\Big(\|x\|^2 > s^2\big(d + 2\sqrt{td} + 2t\big)\Big) \le e^{-t}.$$
--
--   This is the concentration inequality of Hsu, Kakade and Zhang (2012, Theorem 1) for quadratic forms of sub-gaussian random vectors, with $A = I$. The paper applies it to $x = \xi_i - \xi_j$ with $s = \sqrt2\,\sigma_{\max}$ (by (E.5)), which gives the printed form $\mathbb P(\|\xi_i - \xi_j\|^2 > 2\sigma^2_{\max}(d + 2\sqrt{td} + 2t)) \le \exp(-t)$.
--
--   **Formalization Note** The statement is the general cited inequality, of which the page's display is the instance $s = \sqrt 2\sigma_{\max}$; the probability of the event is bounded as an outer measure.
-- source:
--   arXiv:1912.07546v3, Appendix E, display (E.6), p. 40; Hsu, Kakade, Zhang (2012), Theorem 1

import Mathlib
import Definitions.Def_RobustSpecClust_Est_Setting
open MeasureTheory ProbabilityTheory

namespace RobustSpecClust.Est

theorem eq_E6 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (x : Ω → E d) (s : ℝ) (hx : IsSubgaussianVec P x s) (t : ℝ) (ht : 0 < t) :
    P {ω | s ^ 2 * ((d : ℝ) + 2 * Real.sqrt (t * d) + 2 * t) < ‖x ω‖ ^ 2} ≤
      ENNReal.ofReal (Real.exp (-t)) := by sorry

end RobustSpecClust.Est
