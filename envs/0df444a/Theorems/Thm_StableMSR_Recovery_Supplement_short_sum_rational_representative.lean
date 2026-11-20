-- Prove2me | Theorems.Thm_StableMSR_Recovery_Supplement_short_sum_rational_representative
-- name    : StableMSR.Recovery.Supplement.short_sum_rational_representative
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-19T19:56:32.886793+00:00
-- url     : https://prove2.me/theorems/2b66e009-0b57-402d-a82f-f2621da2efd8
-- title:
--   A small common denominator preserving bounded comparisons of coordinate sums
-- statement:
--   Let $x$ be a real vector with $d$ coordinates and let $H\ge1$ be an integer. There is a vector $z/D$ with a single nonzero integer denominator, with $|D|$ and every $|z_i|$ at most $d!(H^2)^d$, which satisfies every weak comparison $q+\sum_{i\in s}x_i\le\sum_{j\in t}x_j$ satisfied by $x$ whenever $s,t$ are lists of total length at most $H$ and the reduced numerator and denominator of $q$ are bounded in magnitude by $H$. Repetitions are allowed. This formulation of the small rational point argument in Lemma C.3 permits simultaneous preservation of equalities, metric triangle inequalities, and comparisons of sums of cluster radii.
-- source:
--   Shyam Ravichandran and Lev Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Appendix C, Lemma C.3, pp. 25–26 (bounded rational polyhedron and determinant argument). https://arxiv.org/abs/2611.03547

import Mathlib

set_option autoImplicit false

namespace StableMSR.Recovery.Supplement

theorem short_sum_rational_representative {ι : Type} [Fintype ι] (x : ι → ℝ) (H : ℕ) (hH : 1 ≤ H) :
    ∃ (D : ℤ) (z : ι → ℤ), D ≠ 0 ∧
      D.natAbs ≤ (Fintype.card ι).factorial * (H ^ 2) ^ Fintype.card ι ∧
      (∀ i, (z i).natAbs ≤ (Fintype.card ι).factorial * (H ^ 2) ^ Fintype.card ι) ∧
      ∀ (s t : List ι) (q : ℚ), s.length + t.length ≤ H →
        q.num.natAbs ≤ H → q.den ≤ H →
        (q : ℝ) + (s.map x).sum ≤ (t.map x).sum →
        (q : ℝ) + (s.map (fun i => ((z i : ℝ) / D))).sum ≤
          (t.map (fun i => ((z i : ℝ) / D))).sum := by sorry

end StableMSR.Recovery.Supplement
