-- Prove2me | Theorems.Thm_QuadMemory_ConvexOpt_proposition_20_rank_one
-- name    : QuadMemory.ConvexOpt.proposition_20_rank_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:04:58.902378+00:00
-- url     : https://prove2.me/theorems/b8b4ebac-acf6-495d-8c65-82c3f577a1e1
-- title:
--   Proposition 20 (second claim), p. 36 — for a rank-one projection P and x uniform on S^{d−1}, P(‖Px‖ ≥ √(t/(d−1))) ≤ 2√t e^{−t/2} for t ≥ 1
-- statement:
--   Let $d\ge2$, let $P$ be the orthogonal projection of $\mathbb R^d$ onto a line, and let $x\sim\mathcal U(S^{d-1})$. Then for every $t\ge1$,
--   $$\mathbb P\Big(\|P(x)\|\ge\sqrt{\frac t{d-1}}\Big)\le2\sqrt t\,e^{-t/2}.$$
--
--   This tail bound controls how much a random unit vector correlates with a fixed direction; Lemma 21 applies it inside the orthogonal complement of the earlier queries.
--
--   **Formalization Note.** The page states this for every $t>0$, which is false for small $t$: at $d=2$, $t=0.01$ the left side is about $0.94$ while the right side is about $0.20$. The proof's Chernoff step needs $t/d\ge1/d$, so the statement is restricted to $t\ge1$; Lemma 21 uses it only for $t\ge4/3$. The projection is orthogonal, as in the proof.
-- source:
--   Blanchard, Zhang & Jaillet, arXiv:2302.04963v2, p. 36, Proposition 20 (second claim), restricted to t ≥ 1

import Mathlib
import Definitions.Def_QuadMemory_ConvexOpt_Model
import Definitions.Def_QuadMemory_ConvexOpt_Game

open MeasureTheory

namespace QuadMemory.ConvexOpt

/-- Proposition 20, second claim (p. 36), for `t ≥ 1`: if `P` is the orthogonal projection of
`ℝ^d` (`d ≥ 2`) onto a line `K` and `x ∼ U(S^{d-1})`, then
`P(‖P x‖ ≥ √(t/(d-1))) ≤ 2 √t e^{-t/2}`. The page states it for every `t > 0`; it is false for
small `t` (at `d = 2`, `t = 0.01` the left side is about `0.94`), and its proof needs `t ≥ 1`. -/
theorem proposition_20_rank_one (d : ℕ) (hd : 2 ≤ d) (K : Submodule ℝ (E d))
    (hK : Module.finrank ℝ K = 1) (t : ℝ) (ht : 1 ≤ t) :
    sphereLaw d {x | Real.sqrt (t / ((d : ℝ) - 1)) ≤ ‖K.starProjection x‖} ≤
      ENNReal.ofReal (2 * Real.sqrt t * Real.exp (-(t / 2))) := by sorry

end QuadMemory.ConvexOpt
