-- Prove2me | Theorems.Thm_PhilipponMultiplicity_Hilbert_hilbertPolynomial_zero_iff_trivial
-- name    : PhilipponMultiplicity.Hilbert.hilbertPolynomial_zero_iff_trivial
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T02:39:02.218734+00:00
-- url     : https://prove2.me/theorems/4328e741-8fe9-4eeb-865d-8837f34d8d9c
-- title:
--   The Hilbert polynomial vanishes exactly for projectively trivial ideals
-- statement:
--   For every multihomogeneous ideal $I$ in the coordinate ring of a product of projective spaces, its actual multigraded Hilbert polynomial is zero exactly when the irrelevant ideal is contained in $\sqrt I$. The original Hilbert polynomial and relevance definitions are used.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, Hilbert foundations in §3, printed pp. 361–363, https://www.numdam.org/articles/10.24033/bsmf.2060/. A granular supporting assertion for the original Section 3 statements; definitions are unchanged.

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.Hilbert.hilbertPolynomial_zero_iff_trivial
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) :
    hilbertPolynomial K M.factorCount M.ambientDimension I = 0 ↔ ¬ IsNontrivialIdeal M I := by sorry
