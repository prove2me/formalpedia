-- Prove2me | Theorems.Thm_QuadMemory_ConvexOpt_proposition_20_concentration
-- name    : QuadMemory.ConvexOpt.proposition_20_concentration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:04:50.072002+00:00
-- url     : https://prove2.me/theorems/fbccf107-502f-4f4c-8ad6-8763a5ce6972
-- title:
--   Proposition 20 (first claim), p. 35 — for x uniform on S^{d−1}, ‖P x‖² deviates from r/d by t with probability at most e^{−dt²}
-- statement:
--   Let $d\ge1$, let $P$ be the orthogonal projection of $\mathbb R^d$ onto a subspace of dimension $r$, and let $x\sim\mathcal U(S^{d-1})$. Then for every $t>0$,
--   $$\max\Big\{\mathbb P\Big(\|P(x)\|^2-\frac rd\ge t\Big),\ \mathbb P\Big(\|P(x)\|^2-\frac rd\le-t\Big)\Big\}\le e^{-dt^2}.$$
--
--   This concentration bound for random projections feeds the anti-concentration estimates for the hidden vectors of the hard instance (Lemma 21).
--
--   **Formalization Note.** "A projection of rank $r$" is read as an orthogonal projection, as in the proof, which rotates it onto the first $r$ coordinates. The probabilities are those of the normalized surface measure.
-- source:
--   Blanchard, Zhang & Jaillet, arXiv:2302.04963v2, p. 35, Proposition 20 (first claim; proof p. 36)

import Mathlib
import Definitions.Def_QuadMemory_ConvexOpt_Model
import Definitions.Def_QuadMemory_ConvexOpt_Game

open MeasureTheory

namespace QuadMemory.ConvexOpt

/-- Proposition 20, first claim (p. 35): if `P` is the orthogonal projection of `ℝ^d` onto a
subspace `K` of dimension `r` and `x ∼ U(S^{d-1})`, then for every `t > 0` both
`P(‖P x‖² - r/d ≥ t)` and `P(‖P x‖² - r/d ≤ -t)` are at most `e^{-d t²}`. -/
theorem proposition_20_concentration (d : ℕ) (hd : 1 ≤ d) (K : Submodule ℝ (E d)) (t : ℝ)
    (ht : 0 < t) :
    sphereLaw d {x | t ≤ ‖K.starProjection x‖ ^ 2 - (Module.finrank ℝ K : ℝ) / d} ≤
        ENNReal.ofReal (Real.exp (-(d * t ^ 2))) ∧
      sphereLaw d {x | ‖K.starProjection x‖ ^ 2 - (Module.finrank ℝ K : ℝ) / d ≤ -t} ≤
        ENNReal.ofReal (Real.exp (-(d * t ^ 2))) := by sorry

end QuadMemory.ConvexOpt
