-- Prove2me | Theorems.Thm_PinnedAsymmetry_asymmetry_indep_K
-- name    : PinnedAsymmetry.asymmetry_indep_K
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-23T22:32:01.341997+00:00
-- url     : https://prove2.me/theorems/79925855-6a1b-4c6e-a773-c724613eb0e9
-- title:
--   The asymmetry is the same for any two stiffnesses $K_1$, $K_2$
-- statement:
--   Let $K_1, K_2, c, \beta, q$ be real numbers, and let
--
--   $$
--   \omega_K(q) = \beta c \sin q + \sqrt{\bigl(\beta c \sin q\bigr)^2 + K + 2c\,(1 - \cos q)}
--   $$
--
--   be the upper-branch frequency on a uniform ring with on-site stiffness $K$. Then
--
--   $$
--   \omega_{K_1}(q) - \omega_{K_1}(-q) = \omega_{K_2}(q) - \omega_{K_2}(-q).
--   $$
--
--   This is the statement in the mission's title: the propagation asymmetry is the same for every value of the on-site stiffness. It follows from the goal, whose right-hand side $2\beta c \sin q$ contains no $K$.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §7, Theorem 7.1: https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", "Related: the pinned asymmetry (Section 7)" (stiffness cancels): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib
import Definitions.Def_PinnedAsymmetry_omega

open Real

namespace PinnedAsymmetry
theorem asymmetry_indep_K (K₁ K₂ c β q : ℝ) :
    omega K₁ c β q - omega K₁ c β (-q) = omega K₂ c β q - omega K₂ c β (-q) := by sorry
end PinnedAsymmetry
