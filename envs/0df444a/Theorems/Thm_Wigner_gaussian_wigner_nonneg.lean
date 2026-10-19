-- Prove2me | Theorems.Thm_Wigner_gaussian_wigner_nonneg
-- name    : Wigner.gaussian_wigner_nonneg
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-18T16:52:25.417866+00:00
-- url     : https://prove2.me/theorems/ad6d50a5-c7b7-423e-b292-ba8affb46283
-- title:
--   Gaussian pure states have nonnegative Wigner function
-- statement:
--   Gaussian pure states have nonnegative Wigner functions: the converse of Hudson's theorem. Let $a, b, c \in \mathbb{C}$ with $\mathrm{Re}(a) > 0$, so that
--
--   $$\psi(x) = e^{-ax^2 + bx + c}$$
--
--   is a square-integrable Gaussian wave packet, and let $\hbar > 0$. Then the Wigner function of $\psi$ is nonnegative at every phase-space point: $W(x,p) \ge 0$ for all $x, p$. The source text notes that "the Wigner function of any such state is a Gaussian distribution on phase space" — coherent and squeezed states are exactly the pure states with classical phase-space pictures.
--
--   **Formalization Note** No normalization of $\psi$ is assumed: positivity is invariant under the scalar factor $e^c$. The hypothesis $\mathrm{Re}(a) > 0$ is the source's assumption and is what makes $\psi$ a genuine wave packet.
-- source:
--   Wikipedia, "Wigner quasiprobability distribution" (oldid 1376057304), section "Positivity of the function". https://en.wikipedia.org/wiki/Wigner_quasiprobability_distribution

import Mathlib
import Definitions.Def_wigner

open MeasureTheory

namespace Wigner

theorem gaussian_wigner_nonneg {a b c : ℂ} {ℏ x p : ℝ} (ha : 0 < Complex.re a)
    (hℏ : 0 < ℏ) :
    0 ≤ wigner (fun y => Complex.exp (-(a * (y : ℂ) ^ 2) + b * (y : ℂ) + c)) ℏ x p := by sorry

end Wigner
