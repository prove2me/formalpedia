-- Prove2me | Theorems.Thm_PhilipponMultiplicity_regular_hypersurface_hilbert_function
-- name    : PhilipponMultiplicity.regular_hypersurface_hilbert_function
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-25T22:37:00.991051+00:00
-- url     : https://prove2.me/theorems/f4797f82-24d6-448c-8ba8-1e240fa0cab2
-- title:
--   Regular hypersurface: exact multigraded Hilbert-function identity
-- statement:
--   Let $I$ be a multihomogeneous ideal in the coordinate ring of a product of projective spaces over any field. Let $P$ be homogeneous of multidegree $D$ and a non-zero-divisor modulo $I$. For every natural multidegree $d$,
--   $$h_{I+(P)}(D+d)+h_I(d)=h_I(D+d).$$
--   Here each Hilbert function is the actual vector-space dimension of the corresponding homogeneous quotient piece. The identity does not assume Hilbert-polynomial existence, positive equation degrees, or nonempty projective support.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, https://www.numdam.org/articles/10.24033/bsmf.2060/, §3 pp. 362–364, Hilbert-polynomial foundations and the exact-sequence proof of Lemma 3.1 on p. 363. Supporting lemma; the parent retains the published positive-equation-degree correction.

import Definitions.Def_PhilipponMultiplicity_SectionThree
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.regular_hypersurface_hilbert_function
    (K : Type*) [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (hregular : IsRegular (Ideal.Quotient.mk I P)) (d : M.FactorIndex → ℕ) :
    hilbertFunction K M.factorCount M.ambientDimension
        (I ⊔ Ideal.span {P}) (D + d) +
      hilbertFunction K M.factorCount M.ambientDimension I d =
    hilbertFunction K M.factorCount M.ambientDimension I (D + d) := by sorry
