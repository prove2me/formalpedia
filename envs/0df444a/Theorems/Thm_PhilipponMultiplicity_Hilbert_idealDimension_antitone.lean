-- Prove2me | Theorems.Thm_PhilipponMultiplicity_Hilbert_idealDimension_antitone
-- name    : PhilipponMultiplicity.Hilbert.idealDimension_antitone
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T01:02:02.263274+00:00
-- url     : https://prove2.me/theorems/88369212-12bd-4ef4-b036-05886e7dfeea
-- title:
--   Hilbert dimension decreases under homogeneous ideal inclusion
-- statement:
--   If $I\subseteq J$ are multihomogeneous ideals in a product-of-projective-spaces coordinate ring over any field, the total degree of the actual Hilbert polynomial of $J$ is at most that of $I$. The existing convention that the zero polynomial has total degree zero is retained.
-- source:
--   Supporting commutative algebra for Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, §3, Lemma 3.2, printed p. 364, https://www.numdam.org/articles/10.24033/bsmf.2060/. Philippon refers to the classical homogeneous argument and van der Waerden (1928), Theorem 8 p. 758 and §32 p. 767. This is a proved intermediate step of that associativity argument, not an additional numbered assertion in Philippon.

import Definitions.Def_PhilipponMultiplicity_SectionThree
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.Hilbert.idealDimension_antitone
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (I J : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hJ : IsMultihomogeneousIdeal M J) (hle : I ≤ J) :
    idealDimension M J ≤ idealDimension M I := by sorry
