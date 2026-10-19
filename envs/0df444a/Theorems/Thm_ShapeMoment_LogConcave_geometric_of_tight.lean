-- Prove2me | Theorems.Thm_ShapeMoment_LogConcave_geometric_of_tight
-- name    : ShapeMoment.LogConcave.geometric_of_tight
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:17.535578+00:00
-- url     : https://prove2.me/theorems/fd79335d-b389-45d2-bb7c-d130691fc8aa
-- title:
--   Proof of Theorem 4.1 — geometric tight interval
-- statement:
--   Suppose $x_j>0$ on the integer interval $[u,v]$ and $x_{j-1}x_{j+1}=x_j^2$ for every interior index $u<j<v$. Then some $r>0$ satisfies
--
--   $$x_j=x_u r^{j-u}\qquad(u\le j\le v).$$
--
--   This is the geometric form used on each piece in equation (15). Equality is imposed only on interior indices.
-- source:
--   Chen, He, Jiang, Ryan & Zhang, The discrete moment problem with nonconvex shape constraints, arXiv:1708.02079v1, p. 15, proof of Theorem 4.1, standard observation

import Mathlib

namespace ShapeMoment.LogConcave

theorem geometric_of_tight (x : ℕ → ℝ) (u v : ℕ) (huv : u ≤ v)
    (hpos : ∀ j, u ≤ j → j ≤ v → 0 < x j)
    (htight : ∀ j, u < j → j < v → x (j - 1) * x (j + 1) = x j ^ 2) :
    ∃ r : ℝ, 0 < r ∧ ∀ j, u ≤ j → j ≤ v → x j = x u * r ^ (j - u) := by sorry

end ShapeMoment.LogConcave
