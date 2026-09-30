-- Prove2me | Theorems.Thm_PhilipponMultiplicity_Hilbert_idealDimension_eq_of_radical_eq
-- name    : PhilipponMultiplicity.Hilbert.idealDimension_eq_of_radical_eq
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T10:00:05.337866+00:00
-- url     : https://prove2.me/theorems/39e7f63c-73f5-4677-9262-24b611f7f689
-- title:
--   Equal radicals give equal multigraded Hilbert dimensions
-- statement:
--   Let $I$ and $J$ be multihomogeneous ideals in the coordinate ring of a product of projective spaces over any field. If $\sqrt I=\sqrt J$, then their actual multigraded Hilbert polynomials have equal total degree. The statement uses the existing Hilbert-polynomial definition, including its convention that the zero polynomial has total degree zero. No relevance, nontriviality, or positive-dimension assumption is required.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs. Support-invariance of the Hilbert dimension implicit in the component comparisons of Section 3, printed pp. 362–366. This granular supporting assertion is proved from homogeneous prime filtrations, not identified with a numbered paper theorem. https://www.numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.Hilbert.idealDimension_eq_of_radical_eq
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
(I J : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hJ : IsMultihomogeneousIdeal M J)
    (heq : I.radical = J.radical) : idealDimension M I = idealDimension M J := by sorry
