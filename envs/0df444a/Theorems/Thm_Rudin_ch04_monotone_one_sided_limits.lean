-- Prove2me | Theorems.Thm_Rudin_ch04_monotone_one_sided_limits
-- name    : Rudin.ch04_monotone_one_sided_limits
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T22:20:15.703003+00:00
-- url     : https://prove2.me/theorems/596bc3a5-58d0-4975-a212-f9ddc5cc2d78
-- title:
--   Theorem 4.29 — one-sided limits of a monotone function
-- statement:
--   Let $f$ be monotonically increasing on $(a,b)$. At every $x \in (a,b)$ the one-sided limits $f(x-)$ and $f(x+)$ exist, equal $\sup_{a<t<x} f(t)$ and $\inf_{x<t<b} f(t)$ respectively, and satisfy $f(x-) \le f(x) \le f(x+)$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 4, p. 95, Theorem 4.29

import Mathlib
import Definitions.Def_Rudin_ch04_continuity

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 4.29: if `f` is monotonically increasing on `(a, b)` then at every point
`x` of `(a, b)` the one-sided limits `f(x-)` and `f(x+)` exist, are given by
`sup_{a<t<x} f t` and `inf_{x<t<b} f t`, and satisfy `f(x-) ≤ f x ≤ f(x+)`. -/
theorem ch04_monotone_one_sided_limits (a b : ℝ) (f : ℝ → ℝ)
    (hf : MonotoneOn f (Set.Ioo a b)) (x : ℝ) (hx : x ∈ Set.Ioo a b) :
    ∃ L R : ℝ,
      Tendsto f (𝓝[<] x) (𝓝 L) ∧ Tendsto f (𝓝[>] x) (𝓝 R) ∧
      IsLUB (f '' Set.Ioo a x) L ∧ IsGLB (f '' Set.Ioo x b) R ∧
      L ≤ f x ∧ f x ≤ R := by sorry

end Rudin
