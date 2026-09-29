-- Prove2me | Theorems.Thm_PinnedAsymmetryQ_radicand_flip
-- name    : PinnedAsymmetryQ.radicand_flip
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-24T04:25:08.272338+00:00
-- url     : https://prove2.me/theorems/a03a2838-4295-4884-8439-57aa0a33034d
-- title:
--   The radicand is unchanged by reversing axis 0
-- statement:
--   For $q \ge 1$, all real $K, c, \beta$ and every $k \in \mathbb{R}^q$, with $\bar k = (-k_0, k_1, \dots, k_{q-1})$,
--
--   $$
--   \bigl(\beta c \sin \bar k_0\bigr)^2 + K + 2c \sum_{a} (1 - \cos \bar k_a) = \bigl(\beta c \sin k_0\bigr)^2 + K + 2c \sum_{a} (1 - \cos k_a).
--   $$
--
--   The quantity under the square root takes the same value for both propagation directions, since $\sin^2(-k_0) = \sin^2 k_0$, $\cos(-k_0) = \cos k_0$, and the transverse terms are untouched.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §7, Theorem 7.1 (extended to q axes): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", "Related: the pinned asymmetry (Section 7)": https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib
import Definitions.Def_PinnedAsymmetryQ_omega

open Real BigOperators

namespace PinnedAsymmetryQ
theorem radicand_flip (q : ℕ) [NeZero q] (K c β : ℝ) (k : Fin q → ℝ) :
    (β * c * sin (flip0 q k 0)) ^ 2 + K + 2 * c * ∑ a : Fin q, (1 - cos (flip0 q k a))
      = (β * c * sin (k 0)) ^ 2 + K + 2 * c * ∑ a : Fin q, (1 - cos (k a)) := by sorry
end PinnedAsymmetryQ
