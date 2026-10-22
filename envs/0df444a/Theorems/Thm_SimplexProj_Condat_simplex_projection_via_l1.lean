-- Prove2me | Theorems.Thm_SimplexProj_Condat_simplex_projection_via_l1
-- name    : SimplexProj.Condat.simplex_projection_via_l1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T23:47:49.969081+00:00
-- url     : https://prove2.me/theorems/6b60da5a-2792-4394-a3a3-8bfb102c957b
-- title:
--   Remark 2.1 — projection onto the simplex via the $\ell_1$ ball
-- statement:
--   Let $N \ge 1$, $a > 0$, and $y, x \in \mathbb{R}^N$. Then:
--
--   1. $P_\Delta(y) = P_\Delta(y + c)$ for every $c \in \mathbb{R}$, where $y + c = (y_1 + c, \dots, y_N + c)$;
--   2. $P_\Delta(y) = P_B(y)$ if the entries of $y$ are nonnegative and $\|y\|_1 = \sum_n |y_n| \ge a$;
--   3. for every $y$, $P_\Delta(y) = P_B(y - y_{\min} + a/N)$, where $y_{\min}$ is the smallest entry of $y$ and the shift is applied to every entry:
--
--   $$P_\Delta(y) = P_B\big(y - y_{\min} + a/N\big).$$
--
--   This is Remark 2.1 of Condat, the converse of Proposition 2.1: any algorithm for the $\ell_1$ ball also projects onto the simplex.
--
--   **Formalization Note.** Each equality of projections $P(u) = Q(w)$ is stated as "$x$ is the projection of $u$ for $P$ if and only if it is the projection of $w$ for $Q$" (`IsSimplexProjection`, `IsL1Projection`), which is equivalent since both projections exist and are unique. $y_{\min}$ is any value with `IsLeast (Set.range y) ymin`.
-- source:
--   Condat, Fast Projection onto the Simplex and the ℓ1 Ball, HAL hal-01056171v2, p. 2, Remark 2.1

import Mathlib
import Definitions.Def_SimplexProj_Condat_IsSimplexProjection
import Definitions.Def_SimplexProj_Condat_IsL1Projection

namespace SimplexProj.Condat

/-- Condat, Remark 2.1 (p. 2): (i) `P_Δ(y) = P_Δ(y + c)` for every `c ∈ ℝ`; (ii) `P_Δ(y) = P_B(y)`
if the elements of `y` are nonnegative and `‖y‖₁ ≥ a`; (iii) for every `y`,
`P_Δ(y) = P_B(y - y_min + a/N)`, where `y_min` is the smallest element of `y`. Each equality of
projections is stated as: `x` is the one projection iff it is the other. Standing assumptions of
p. 1: `N ≥ 1`, `a > 0`. -/
theorem simplex_projection_via_l1 (N : ℕ) (hN : 1 ≤ N) (a : ℝ) (ha : 0 < a)
    (y x : Fin N → ℝ) :
    (∀ c : ℝ, IsSimplexProjection a y x ↔ IsSimplexProjection a (fun n => y n + c) x) ∧
    ((∀ n, 0 ≤ y n) → a ≤ ∑ n, |y n| →
      (IsSimplexProjection a y x ↔ IsL1Projection a y x)) ∧
    (∀ ymin : ℝ, IsLeast (Set.range y) ymin →
      (IsSimplexProjection a y x ↔ IsL1Projection a (fun n => y n - ymin + a / N) x)) := by sorry

end SimplexProj.Condat
