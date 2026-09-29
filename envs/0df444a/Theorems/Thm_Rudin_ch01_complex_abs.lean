-- Prove2me | Theorems.Thm_Rudin_ch01_complex_abs
-- name    : Rudin.ch01_complex_abs
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T18:41:30.059013+00:00
-- url     : https://prove2.me/theorems/579f1561-8e10-4758-a8b9-dbf042b1ff21
-- title:
--   Theorem 1.33 — properties of the complex absolute value
-- statement:
--   For complex numbers $z, w$: $|z| \ge 0$, with $|z| = 0$ if and only if $z = 0$; $|\bar z| = |z|$; $|zw| = |z||w|$; $|\operatorname{Re} z| \le |z|$; and $|z + w| \le |z| + |w|$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 1, p. 14, Theorem 1.33

import Mathlib

namespace Rudin

/-- Rudin, Theorem 1.33: the basic properties of the absolute value `|z| = ‖z‖` of a complex
number: positivity and nondegeneracy, invariance under conjugation, multiplicativity, the bound
`|Re z| ≤ |z|`, and the triangle inequality. -/
theorem ch01_complex_abs (z w : ℂ) :
    0 ≤ ‖z‖ ∧
    (‖z‖ = 0 ↔ z = 0) ∧
    ‖(starRingEnd ℂ) z‖ = ‖z‖ ∧
    ‖z * w‖ = ‖z‖ * ‖w‖ ∧
    |z.re| ≤ ‖z‖ ∧
    ‖z + w‖ ≤ ‖z‖ + ‖w‖ := by sorry

end Rudin
