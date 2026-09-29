-- Prove2me | Theorems.Thm_Rudin_ch04_intermediate_value
-- name    : Rudin.ch04_intermediate_value
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T22:16:36.192116+00:00
-- url     : https://prove2.me/theorems/e8b0e04c-f0b9-483e-b965-0595384a3436
-- title:
--   Theorem 4.23 — intermediate value theorem
-- statement:
--   Let $f$ be a continuous real function on $[a,b]$ with $a < b$. If $f(a) < c < f(b)$, then there is a point $x \in (a,b)$ with $f(x) = c$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 4, p. 93, Theorem 4.23

import Mathlib
import Definitions.Def_Rudin_ch04_continuity

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 4.23 (intermediate value theorem): if `f` is a continuous real function on
`[a, b]`, `f a < c < f b`, then `f x = c` for some `x` in `(a, b)`. -/
theorem ch04_intermediate_value (a b : ℝ) (hab : a < b) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) (c : ℝ) (hc : f a < c ∧ c < f b) :
    ∃ x ∈ Set.Ioo a b, f x = c := by sorry

end Rudin
