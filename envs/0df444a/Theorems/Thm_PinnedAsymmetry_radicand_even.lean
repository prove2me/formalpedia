-- Prove2me | Theorems.Thm_PinnedAsymmetry_radicand_even
-- name    : PinnedAsymmetry.radicand_even
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-23T22:30:18.941625+00:00
-- url     : https://prove2.me/theorems/de89fc8e-143f-461e-befa-c66f722e0745
-- title:
--   The radicand is the same at $q$ and $-q$
-- statement:
--   For all real $K, c, \beta, q$,
--
--   $$
--   \bigl(\beta c \sin(-q)\bigr)^2 + K + 2c\,\bigl(1 - \cos(-q)\bigr) = \bigl(\beta c \sin q\bigr)^2 + K + 2c\,\bigl(1 - \cos q\bigr).
--   $$
--
--   The quantity under the square root in $\omega(q)$ takes the same value in both propagation directions. This is why the stiffness $K$ cancels from the asymmetry.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §7, Theorem 7.1: https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", "Related: the pinned asymmetry (Section 7)": https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib

open Real

namespace PinnedAsymmetry
theorem radicand_even (K c β q : ℝ) :
    (β * c * sin (-q)) ^ 2 + K + 2 * c * (1 - cos (-q))
      = (β * c * sin q) ^ 2 + K + 2 * c * (1 - cos q) := by sorry
end PinnedAsymmetry
