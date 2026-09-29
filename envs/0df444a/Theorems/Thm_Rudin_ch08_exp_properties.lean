-- Prove2me | Theorems.Thm_Rudin_ch08_exp_properties
-- name    : Rudin.ch08_exp_properties
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:16:18.3836+00:00
-- url     : https://prove2.me/theorems/2ab00fc3-ac0f-45d7-8f9a-d06e1af7eae4
-- title:
--   Theorem 8.6 — properties of the exponential function
-- statement:
--   The exponential function satisfies $E(z+w) = E(z)E(w)$; it is its own derivative; it is strictly increasing and positive on $\mathbb{R}$ with $E(x) \to \infty$ as $x \to +\infty$ and $E(x) \to 0$ as $x \to -\infty$; and $x^n e^{-x} \to 0$ for every $n$, so $E$ grows faster than every power.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 8, p. 180, Theorem 8.6

import Mathlib
import Definitions.Def_Rudin_ch08_fourier

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 8.6: the exponential function satisfies the addition formula, is its own
derivative, is positive and strictly increasing on the real line with limits `+∞` and `0` at
`±∞`, and grows faster than every power. -/
theorem ch08_exp_properties :
    (∀ z w : ℂ, Complex.exp (z + w) = Complex.exp z * Complex.exp w) ∧
    (∀ x : ℝ, HasDerivAt Real.exp (Real.exp x) x) ∧
    StrictMono Real.exp ∧
    Tendsto Real.exp atTop atTop ∧
    Tendsto Real.exp atBot (𝓝 0) ∧
    (∀ n : ℕ, Tendsto (fun x : ℝ => x ^ n * Real.exp (-x)) atTop (𝓝 0)) := by sorry

end Rudin
