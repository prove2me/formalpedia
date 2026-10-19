-- Prove2me | Theorems.Thm_Wigner_fock_wigner
-- name    : Wigner.fock_wigner
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-18T16:51:11.886871+00:00
-- url     : https://prove2.me/theorems/24fc375e-5c43-49eb-a9fe-0a769d0adff5
-- title:
--   Groenewold's formula for the Wigner function of a Fock state
-- statement:
--   Groenewold's closed formula for the Wigner function of a Fock state. Let $|m\rangle$ be the $m$-th number state of the harmonic oscillator, with normalized wavefunction $u_m(x) = (2^m m!)^{-1/2}\pi^{-1/4}H_m(x)e^{-x^2/2}$, in the dimensionless phase-space units of the source ($\hbar = 1$). Then
--
--   $$W_{|m\rangle}(x,p) = \frac{(-1)^m}{\pi} e^{-(x^2+p^2)}\, L_m\!\big(2(x^2+p^2)\big),$$
--
--   where $L_m$ denotes the $m$-th Laguerre polynomial. This formula was discovered by H. J. Groenewold in 1946 and is the source text's central worked example: through the oscillation of the Laguerre polynomial it exhibits the negativity of the Wigner function for excited number states.
--
--   **Formalization Note** The statement is an equation between real-valued quantities depending on $(m, x, p)$; the reduced-Planck-constant slot of the Wigner function is fixed to $1$, matching the source's dimensionless variables, and the Fock state is the normalized one (the source's displayed $u_m$ omits the factor $(2^m m!)^{-1/2}$, but its formula is stated for the normalized number states).
-- source:
--   Wikipedia, "Wigner quasiprobability distribution" (oldid 1376057304), section "Examples" (Groenewold 1946 formula). Primary source: H. J. Groenewold, Physica 12(7), 405-460 (1946), doi:10.1016/S0031-8914(46)80059-4. https://en.wikipedia.org/wiki/Wigner_quasiprobability_distribution

import Mathlib
import Definitions.Def_wigner
import Definitions.Def_wigner_states

open MeasureTheory

namespace Wigner

theorem fock_wigner (m : ℕ) (x p : ℝ) :
    wigner (fockState m) 1 x p =
      (-1 : ℝ) ^ m / Real.pi * Real.exp (-(x ^ 2 + p ^ 2)) *
        laguerreL m (2 * (x ^ 2 + p ^ 2)) := by sorry

end Wigner
