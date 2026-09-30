-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_finite_elementary_locus_vanishing
-- name    : WeierstrassEllipticZeta.finite_elementary_locus_vanishing
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-21T16:35:05.906572+00:00
-- url     : https://prove2.me/theorems/0d85f1e1-6c11-46f4-8278-88c0ac3aa265
-- title:
--   Finite vanishing tests for elementary affine loci
-- statement:
--   Let Q be a polynomial in the mission's seven projective coordinates, homogeneous
--   of degree m in the first two and of degree n in the last five. Let S be any
--   five complex-valued functions. For every elementary shape and complex anchor r:
--
--   1. The finite sample set is contained in the elementary affine locus.
--   2. Its cardinality is exactly 1 for a point, m+n+1 for a line, and
--      (m+1)(n+1) for a whole fibre.
--   3. Q vanishes in the mission's covering-coordinate evaluation at every point
--      of the locus if and only if it vanishes at every displayed sample.
--
--   The result includes m=0, n=0, arbitrary line slopes, arbitrary anchors, and
--   degenerate coordinate values. It needs no analyticity or nonvanishing assumption
--   on S. This is a finite certificate for a fixed proposed locus; it does not
--   establish the existence of the locus satisfying the open global cost bound.
-- source:
--   Derived finite interpolation criterion for the mission's elementary locus-vanishing condition. At a fixed elliptic coordinate, substituting univariate polynomials T,U gives degree at most m*deg(T)+n*deg(U). The line restriction has degree at most m+n and is tested at m+n+1 integer parameters. A whole fibre is tested on an (m+1) by (n+1) integer grid, using the separate degree bounds m and n. The proof uses Mathlib's polynomial root-count theorem, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Roots.lean. This is supporting coordinate algebra for the locus-selection framework, not a claim that Philippon (1986), section 5, is fully formalized: https://www.numdam.org/item/10.24033/bsmf.2060.pdf. No platform theorem dependencies are used by the complete proof. The forward sketch and full converse preserve all witnesses, the local cost, and C. Selecting a successful complex anchor/slope and proving the global cost bound remain open; the finite sample count is not an integer-search bound.

import Definitions.Def_WeierstrassEllipticZeta_ElementaryLocusSamples
import Mathlib.Algebra.MvPolynomial.Eval

open WeierstrassEllipticZeta
open scoped Classical

theorem WeierstrassEllipticZeta.finite_elementary_locus_vanishing
    (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    ∀ (shape : ElementaryLocusShape) (r : Fin 3 → ℂ),
      ↑(elementaryLocusSamples shape r m n) ⊆ elementaryLocus shape r ∧
      (elementaryLocusSamples shape r m n).card =
        (match shape with
          | .point => 1
          | .line _ => m + n + 1
          | .fibre => (m + 1) * (n + 1)) ∧
      ((∀ w ∈ elementaryLocus shape r,
        MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
          S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) ↔
       (∀ w ∈ elementaryLocusSamples shape r m n,
        MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
          S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0)) := by sorry
