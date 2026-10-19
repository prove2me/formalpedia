-- Prove2me | Theorems.Thm_Wigner_wigner_real
-- name    : Wigner.wigner_real
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-18T16:49:37.802925+00:00
-- url     : https://prove2.me/theorems/5d7bcf1e-876a-4337-8f74-0dcfd565212f
-- title:
--   Reality of the Wigner function
-- statement:
--   The Wigner function is real-valued. Let $\psi : \mathbb{R} \to \mathbb{C}$ be a wavefunction, $\hbar > 0$ the reduced Planck constant, and $(x, p)$ a point of phase space, and assume the defining integral exists, that is, the map $y \mapsto \overline{\psi(x+y)}\,\psi(x-y)\,e^{2ipy/\hbar}$ is Lebesgue-integrable over $\mathbb{R}$. Then
--
--   $$\int_{-\infty}^{\infty}\overline{\psi(x+y)}\,\psi(x-y)\,e^{2ipy/\hbar}\,dy \in \mathbb{R},$$
--
--   i.e. its imaginary part vanishes.
--
--   This is Property 1 of the Wigner function in the source text. It is what allows the Wigner function to be a real quantity, and it holds for every wavefunction for which the integral exists: the substitution $y \mapsto -y$ exhibits the integral as its own complex conjugate.
--
--   **Formalization Note** The statement is expressed through the imaginary part of the defining integral Wigner.wignerIntegral; the Wigner function itself is defined as the real part of the same integral, so this milestone discharges exactly the discarded imaginary part.
-- source:
--   Wikipedia, "Wigner quasiprobability distribution" (oldid 1376057304), section "Mathematical properties", Property 1. https://en.wikipedia.org/wiki/Wigner_quasiprobability_distribution

import Mathlib
import Definitions.Def_wigner

open MeasureTheory

namespace Wigner

theorem wigner_real {ψ : ℝ → ℂ} {ℏ x p : ℝ} (hℏ : 0 < ℏ)
    (hint : Integrable (fun y => wignerIntegrand ψ ℏ x p y) volume) :
    (wignerIntegral ψ ℏ x p).im = 0 := by sorry

end Wigner
