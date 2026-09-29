-- Prove2me | Theorems.Thm_PinnedAsymmetryQ_asymmetry
-- name    : PinnedAsymmetryQ.asymmetry
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-24T04:26:04.901317+00:00
-- url     : https://prove2.me/theorems/0dfa01d1-0418-496b-ab03-b2853181e8fb
-- title:
--   The propagation asymmetry $\omega(k) - \omega(\bar k) = 2\beta c \sin k_0$ on a $q$-dimensional lattice
-- statement:
--   Let $q \ge 1$, let $K, c, \beta$ be real and $k \in \mathbb{R}^q$, with $\bar k = (-k_0, k_1, \dots, k_{q-1})$ and
--
--   $$
--   \omega(k) = \beta c \sin k_0 + \sqrt{\bigl(\beta c \sin k_0\bigr)^2 + K + 2c \sum_{a} (1 - \cos k_a)} .
--   $$
--
--   Then
--
--   $$
--   \omega(k) - \omega(\bar k) = 2\beta c \sin k_0 .
--   $$
--
--   Neither the stiffness $K$ nor any transverse wavenumber appears in the asymmetry. The statement concerns the linear asymmetry on a uniform lattice, with the gauge term along one axis.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §7, Theorem 7.1 (extended to q axes): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", "Related: the pinned asymmetry (Section 7)": https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib
import Definitions.Def_PinnedAsymmetryQ_omega

open Real BigOperators

namespace PinnedAsymmetryQ
theorem asymmetry (q : ℕ) [NeZero q] (K c β : ℝ) (k : Fin q → ℝ) :
    omega q K c β k - omega q K c β (flip0 q k) = 2 * β * c * sin (k 0) := by sorry
end PinnedAsymmetryQ
