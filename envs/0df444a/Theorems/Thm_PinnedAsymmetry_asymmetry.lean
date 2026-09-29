-- Prove2me | Theorems.Thm_PinnedAsymmetry_asymmetry
-- name    : PinnedAsymmetry.asymmetry
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-23T22:31:11.630286+00:00
-- url     : https://prove2.me/theorems/06c5eea9-46bc-495b-812f-0a1253e15fed
-- title:
--   The propagation asymmetry $\omega(q) - \omega(-q) = 2\beta c \sin q$ is independent of $K$
-- statement:
--   Let $K, c, \beta, q$ be real numbers, and let
--
--   $$
--   \omega(q) = \beta c \sin q + \sqrt{\bigl(\beta c \sin q\bigr)^2 + K + 2c\,(1 - \cos q)}
--   $$
--
--   be the upper-branch frequency on a uniform ring. Then
--
--   $$
--   \omega(q) - \omega(-q) = 2\beta c \sin q .
--   $$
--
--   The difference between the two propagation directions contains no $K$: the asymmetry is pinned, even though each frequency depends on the on-site stiffness. The statement concerns the linear asymmetry on a uniform lattice only.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §7, Theorem 7.1: https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", "Related: the pinned asymmetry (Section 7)": https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib
import Definitions.Def_PinnedAsymmetry_omega

open Real

namespace PinnedAsymmetry
theorem asymmetry (K c β q : ℝ) :
    omega K c β q - omega K c β (-q) = 2 * β * c * sin q := by sorry
end PinnedAsymmetry
