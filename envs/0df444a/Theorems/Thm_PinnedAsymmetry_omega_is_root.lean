-- Prove2me | Theorems.Thm_PinnedAsymmetry_omega_is_root
-- name    : PinnedAsymmetry.omega_is_root
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-23T22:30:01.375821+00:00
-- url     : https://prove2.me/theorems/8d5c056c-4762-4b8c-8ae1-66fcd9a5d1e9
-- title:
--   $\omega(q)$ solves the dispersion relation
-- statement:
--   Let $K, c, \beta, q$ be real numbers with
--
--   $$
--   \bigl(\beta c \sin q\bigr)^2 + K + 2c\,(1 - \cos q) \ge 0 .
--   $$
--
--   Then the upper-branch frequency $\omega = \omega(q) = \beta c \sin q + \sqrt{(\beta c \sin q)^2 + K + 2c(1-\cos q)}$ satisfies the dispersion relation
--
--   $$
--   \omega^2 - 2\beta c \sin q\;\omega - \bigl(K + 2c\,(1 - \cos q)\bigr) = 0 .
--   $$
--
--   This ties the formula to the physics: it shows $\omega(q)$ is a genuine branch frequency of the model, so that the goal is a statement about the physical frequency rather than an arbitrary expression.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §7, Theorem 7.1: https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", "Related: the pinned asymmetry (Section 7)": https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib
import Definitions.Def_PinnedAsymmetry_omega

open Real

namespace PinnedAsymmetry
theorem omega_is_root (K c β q : ℝ)
    (h : 0 ≤ (β * c * sin q) ^ 2 + K + 2 * c * (1 - cos q)) :
    (omega K c β q) ^ 2 - 2 * β * c * sin q * omega K c β q
      - (K + 2 * c * (1 - cos q)) = 0 := by sorry
end PinnedAsymmetry
