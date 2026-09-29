-- Prove2me | Theorems.Thm_PinnedAsymmetryQ_omega_is_root
-- name    : PinnedAsymmetryQ.omega_is_root
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-24T04:24:42.616071+00:00
-- url     : https://prove2.me/theorems/bceaecb7-e6e1-4ebb-ac05-f40b2088fbc7
-- title:
--   $\omega(k)$ solves the $q$-dimensional dispersion relation
-- statement:
--   Let $q \ge 1$, let $K, c, \beta$ be real, $k \in \mathbb{R}^q$, and suppose
--
--   $$
--   \bigl(\beta c \sin k_0\bigr)^2 + K + 2c \sum_{a} (1 - \cos k_a) \ge 0 .
--   $$
--
--   Then $\omega = \omega(k)$ satisfies
--
--   $$
--   \omega^2 - 2\beta c \sin k_0\;\omega - \Bigl(K + 2c \sum_{a} (1 - \cos k_a)\Bigr) = 0,
--   $$
--
--   so the formula is a genuine branch frequency of the $q$-dimensional dispersion relation.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §7, Theorem 7.1 (extended to q axes): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", "Related: the pinned asymmetry (Section 7)": https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib
import Definitions.Def_PinnedAsymmetryQ_omega

open Real BigOperators

namespace PinnedAsymmetryQ
theorem omega_is_root (q : ℕ) [NeZero q] (K c β : ℝ) (k : Fin q → ℝ)
    (h : 0 ≤ (β * c * sin (k 0)) ^ 2 + K + 2 * c * ∑ a : Fin q, (1 - cos (k a))) :
    (omega q K c β k) ^ 2 - 2 * β * c * sin (k 0) * omega q K c β k
      - (K + 2 * c * ∑ a : Fin q, (1 - cos (k a))) = 0 := by sorry
end PinnedAsymmetryQ
