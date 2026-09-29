-- Prove2me | Theorems.Thm_Rudin_ch08_bohr_mollerup
-- name    : Rudin.ch08_bohr_mollerup
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:32:10.063878+00:00
-- url     : https://prove2.me/theorems/03e387a6-283e-4d23-b7fb-352964c81c5d
-- title:
--   Theorem 8.19 — Bohr–Mollerup characterization of $\Gamma$
-- statement:
--   If $f$ is positive on $(0,\infty)$, $f(1) = 1$, $f(x+1) = x f(x)$, and $\log f$ is convex, then $f = \Gamma$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 8, p. 193, Theorem 8.19

import Mathlib
import Definitions.Def_Rudin_ch08_fourier

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 8.19 (Bohr–Mollerup): a positive function `f` on `(0, ∞)` with
`f 1 = 1`, `f (x + 1) = x f x` and `log f` convex is the Gamma function. -/
theorem ch08_bohr_mollerup (f : ℝ → ℝ) (hpos : ∀ x : ℝ, 0 < x → 0 < f x)
    (hone : f 1 = 1) (hrec : ∀ x : ℝ, 0 < x → f (x + 1) = x * f x)
    (hconv : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x => Real.log (f x))) :
    ∀ x : ℝ, 0 < x → f x = Real.Gamma x := by sorry

end Rudin
