-- Prove2me | Theorems.Thm_Rudin_ch08_abel
-- name    : Rudin.ch08_abel
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T20:13:41.580322+00:00
-- url     : https://prove2.me/theorems/6ebb3051-0cd7-4a50-bc8a-4b8c6e908e1f
-- title:
--   Theorem 8.2 — Abel's limit theorem
-- statement:
--   If $\sum c_n$ converges to $C$ and $f(x) = \sum c_n x^n$ for $|x| < 1$, then $f(x) \to C$ as $x \to 1^-$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 8, p. 174, Theorem 8.2

import Mathlib
import Definitions.Def_Rudin_ch03_series

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 8.2 (Abel's theorem): if `∑ cₙ` converges to `C` and `f x = ∑ cₙ xⁿ` for
`|x| < 1`, then `f x → C` as `x → 1⁻`. -/
theorem ch08_abel (c : ℕ → ℝ) (C : ℝ) (hC : SeriesConvergesTo c C) (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, |x| < 1 → SeriesConvergesTo (fun n => c n * x ^ n) (f x)) :
    Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 C) := by sorry

end Rudin
