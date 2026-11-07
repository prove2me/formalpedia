-- Prove2me | Theorems.Thm_RobustFcstAgg_lemma_10
-- name    : RobustFcstAgg.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:46:06.093934+00:00
-- url     : https://prove2.me/theorems/51736cab-f89f-44a0-8c00-b90130c8490d
-- title:
--   Lemma 10 — the minimum on $[1,n]$ is $2/(q(n)^d+q(n)^{-d})$, attained only by $\hat T_d$
-- statement:
--   Let $n\ge2$ and $q(n)=\frac{\sqrt n+1}{\sqrt n-1}$. Then
--   $$\min_{p\in P_d,\ p(0)=1}\ \max_{x\in[1,n]}|p(x)|=\frac{2}{q(n)^d+q(n)^{-d}},\tag{8}$$
--   and the polynomial $\hat T_d$ achieves the minimax value and is the only polynomial that does.
--
--   This gives the exact value of the continuous problem, and hence the upper bound on the discrete one.
--
--   Differences from the source:
--   - encoding: n unrestricted in q(n) and d²/(n−1) → 2 ≤ n; reason: those expressions are undefined at n = 1
--   - reading: the polynomial T̂_d which achieves the minimax value is unique → T̂_d, given by the formula in the proof on p.29, is a minimizer and every minimizer equals it; reason: the statement names the polynomial that the proof defines
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Lemma 10, Eq. (8), p.29

import Mathlib
import Definitions.Def_RobustFcstAgg_ivlSet
import Definitions.Def_RobustFcstAgg_IsIvlMinimizer
import Definitions.Def_RobustFcstAgg_qn
import Definitions.Def_RobustFcstAgg_chebHat
open Polynomial

namespace RobustFcstAgg

/-- **Lemma 10.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Lemma 10, Eq. (8), p.29: with `q(n) = (√n + 1)/(√n − 1)`,
`min_{p ∈ P_d, p(0) = 1} max_{x ∈ [1,n]} |p(x)| = 2/(q(n)^d + q(n)^{−d})`, and the polynomial `T̂_d` which achieves the minimax value is
unique.

**Formalization Note.** `n ≥ 2`, since `q(1)` is undefined. -/
theorem lemma_10 (n d : ℕ) (hn : 2 ≤ n) :
    IsLeast (ivlSet n d) (2 / (qn n ^ d + (qn n ^ d)⁻¹)) ∧
    IsIvlMinimizer n d (chebHat n d) ∧
    ∀ p : ℝ[X], IsIvlMinimizer n d p → p = chebHat n d := by sorry

end RobustFcstAgg
