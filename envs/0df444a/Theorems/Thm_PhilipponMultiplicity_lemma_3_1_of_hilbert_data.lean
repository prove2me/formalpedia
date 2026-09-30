-- Prove2me | Theorems.Thm_PhilipponMultiplicity_lemma_3_1_of_hilbert_data
-- name    : PhilipponMultiplicity.lemma_3_1_of_hilbert_data
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-25T22:36:46.498284+00:00
-- url     : https://prove2.me/theorems/56b00b33-042e-4d8a-a365-a22b306a7963
-- title:
--   Lemma 3.1: complete degree calculation from Hilbert data
-- statement:
--   For a multihomogeneous ideal $I$ of positive Hilbert-polynomial degree, assume the actual quotient Hilbert polynomial exists, its leading coefficients are nonnegative, and its leading monomials have block exponents bounded by the ambient projective dimensions. If $P$ is regular modulo $I$ and homogeneous of strictly positive multidegree $D$, then both formulas of the corrected Lemma 3.1 hold: the explicit hypersurface coefficient sum at every positive multidegree $d$, and
--   $$H(I+(P);D)=H(I;D).$$
--   All Hilbert polynomials and degrees are computed from actual quotients; the assumptions are the separately stated general Hilbert foundations.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, https://www.numdam.org/articles/10.24033/bsmf.2060/, §3 pp. 362–364, Hilbert-polynomial foundations and the exact-sequence proof of Lemma 3.1 on p. 363. Supporting lemma; the parent retains the published positive-equation-degree correction.

import Definitions.Def_PhilipponMultiplicity_SectionThree
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.lemma_3_1_of_hilbert_data
    (K : Type*) [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (hexists : ∃ F, Hilbert.IsHilbertPolynomial K M.factorCount M.ambientDimension I F)
    (hpositive : ∀ b, 0 ≤ coeff b (homogeneousComponent
      (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I).totalDegree
      (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I)))
    (hbounded : ∀ b : M.FactorIndex →₀ ℕ, (∃ i, M.ambientDimension i < b i) →
      coeff b (homogeneousComponent
        (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I).totalDegree
        (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I)) = 0)
    (ha : 0 < idealDimension M I)
    (D : M.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i)
    (P : M.CoordinateRing) (hP : M.IsHomogeneous P D)
    (hregular : IsRegular (Ideal.Quotient.mk I P)) :
    (∀ d : M.FactorIndex → ℕ, (∀ i, 1 ≤ d i) →
      idealDegreeValue M (I ⊔ Ideal.span {P}) d = hypersurfaceCoefficientSum M I D d) ∧
    idealDegreeValue M (I ⊔ Ideal.span {P}) D = idealDegreeValue M I D := by sorry
