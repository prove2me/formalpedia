-- Prove2me | Theorems.Thm_Viterbo_exists_systolicRatio_eq_one_not_isSymplectomorphic_ball
-- name    : Viterbo.exists_systolicRatio_eq_one_not_isSymplectomorphic_ball
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T09:38:23.659669+00:00
-- url     : https://prove2.me/theorems/fb2847f9-a92a-4fd1-9cc1-34429e4e6afe
-- title:
--   Remark 1.8 — for every n ≥ 2 a convex domain with systolic ratio 1 is not symplectomorphic to a ball
-- statement:
--   For every $n \ge 2$ there is a convex domain $C \subset \mathbb R^{2n}$ with $\mathrm{Sys}(C) = 1$ whose interior is not the image of any Euclidean ball $B^{2n}(r)$ under a symplectic embedding.
--
--   *Formalization note.* "Symplectomorphic" is stated for the interior of the domain, which is open like the ball.
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. (2) 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), pp. 7–8, Remark 1.8

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo

namespace Viterbo

theorem exists_systolicRatio_eq_one_not_isSymplectomorphic_ball (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : Set (OAI.SymmetricPolar.Phase n), IsConvexDomain C ∧ systolicRatio C = 1 ∧
      ∀ c : ℝ, 0 < c → ¬ IsSymplectomorphic (OAI.SymmetricPolar.capacityBall n c) (interior C) := by
  sorry

end Viterbo
