-- Prove2me | Theorems.Thm_QuadMemory_ConvexOpt_lemma_7
-- name    : QuadMemory.ConvexOpt.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:58.230756+00:00
-- url     : https://prove2.me/theorems/438ff9d5-3d27-444e-97e9-862bf7268ec0
-- title:
--   Lemma 7, p. 11 — at any time of Procedure 1, l ≤ r ≤ k, so every period constructs l_p ≤ k vectors
-- statement:
--   Let $1\le k\le d/3-1$ with $p_{max}\ge1$, and let the discretization $\mathcal D_\delta$ have cells of diameter at most $\delta=1/d^3$. For every algorithm $alg$, every matrix $A$ and every realization of the hints of positive probability, at any time of Procedure 1 the counters satisfy
--   $$l\le r\le k .$$
--   In particular, $l_p\le k$ for all periods $p\le p_{max}$.
--
--   Each period therefore constructs at most $k$ hidden vectors, and the whole construction at most $kp_{max}\le d$; the reduction to Game 2 relies on this count.
--
--   **Formalization Note.** The bound $r\le k$ holds by construction; the content is $l\le r$, which the proof derives from the slab and diameter properties of the earlier hints, hence the restriction to hint realizations of positive probability (almost surely). The standing assumptions of §3 ($1\le k\le d/3-1$, $\delta=1/d^3$, $p_{max}$ from (3) and at least one period) are hypotheses.
-- source:
--   Blanchard, Zhang & Jaillet, arXiv:2302.04963v2, p. 11, Lemma 7 (proof pp. 11–12)

import Mathlib
import Definitions.Def_QuadMemory_ConvexOpt_Model
import Definitions.Def_QuadMemory_ConvexOpt_Game
import Definitions.Def_QuadMemory_ConvexOpt_Procedure

namespace QuadMemory.ConvexOpt

/-- Lemma 7 (p. 11): let `1 ≤ k ≤ d/3 - 1` with `p_max ≥ 1`, and let the discretization have cells
of diameter at most `δ = 1/d³`. For every algorithm, every `A` and every hint stream of positive
probability, at any time of Procedure 1 the counters satisfy `l ≤ r` (and `r ≤ k`); in particular
`l_p ≤ k` for every period. -/
theorem lemma_7 (d k M : ℕ) (hk1 : 1 ≤ k) (hk : (k : ℝ) ≤ (d : ℝ) / 3 - 1) (hp : 1 ≤ pmax d k)
    (D : SphereDisc d) (hD : D.DiamLe (1 / (d : ℝ) ^ 3)) (alg : MemAlg d M)
    (A : SignMatrix d) (w : Fin d → D.ι) (hw : procWeight alg k D A w ≠ 0) (t : ℕ) :
    (procRun alg k D A w t).l ≤ (procRun alg k D A w t).r ∧
      (procRun alg k D A w t).r ≤ k := by sorry

end QuadMemory.ConvexOpt
