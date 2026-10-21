-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P04_optical_theorem
-- name    : QAlgorithms.Papers.Independent.Support21.P04.optical_theorem
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:29:06.298992+00:00
-- url     : https://prove2.me/theorems/345482f1-3357-406f-8538-b15118febcf2
-- title:
--   Two-channel optical theorem with the Landauer–Büttiker transition normalization
-- statement:
--   At a fixed energy, let $S\in U(2)$ be the complex unitary scattering matrix. Define its transition matrix by
--
--   $$
--   T=\frac{I_2-S}{2\pi i},
--   $$
--
--   where $I_2$ is the two-dimensional identity and $i^2=-1$. If $T^*$ denotes the conjugate transpose, then
--
--   $$
--   T-T^*=-2\pi i\,TT^*.
--   $$
--
--   This is the optical theorem for the normalization used in the paper's Landauer–Büttiker formulas. It is a fixed-energy algebraic consequence of unitarity; it requires no time-reversal symmetry.
--
--   **Formalization Note** The transition matrix is computed from $S$, rather than supplied as an independent matrix or constrained by an assumed optical identity.
-- source:
--   A general proof of Landauer-Büttiker formula, arXiv:math-ph/0603030v4, PDF p. 5, Equations (15)–(17)

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P04

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P04

/-- Nenciu, PDF p.5, equation (17), with the normalization (15): unitarity of
the two-channel scattering matrix implies the optical theorem. The star in
the source is the complex conjugate transpose, and the product order is T T*. -/
theorem optical_theorem (S : Matrix.unitaryGroup (Fin 2) ℂ) :
    transitionMatrix S - (transitionMatrix S).conjTranspose =
      (-2 * (Real.pi : ℂ) * Complex.I) •
        (transitionMatrix S * (transitionMatrix S).conjTranspose) := by sorry

end QAlgorithms.Papers.Independent.Support21.P04

end
