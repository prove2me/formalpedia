-- Prove2me | Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_top_coefficients
-- name    : PhilipponMultiplicity.multigraded_hilbert_polynomial_top_coefficients
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-25T22:36:54.975437+00:00
-- url     : https://prove2.me/theorems/0f0b3338-0c2d-400e-95c9-bce4829de6a3
-- title:
--   Leading multigraded Hilbert coefficients: positivity and ambient support
-- statement:
--   For every homogeneous ideal $I$ in the block-graded coordinate ring of a product of projective spaces over a field, the leading homogeneous part of its actual Hilbert polynomial has nonnegative rational coefficients. Its coefficient at an exponent $b$ is zero whenever some $b_i$ exceeds the ambient projective dimension $N_i$. The existing zero-fallback convention is retained; no Hilbert polynomial or degree is assigned as additional data.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, https://www.numdam.org/articles/10.24033/bsmf.2060/, §3 pp. 362–364, Hilbert-polynomial foundations and the exact-sequence proof of Lemma 3.1 on p. 363. Supporting lemma; the parent retains the published positive-equation-degree correction.

import Definitions.Def_PhilipponMultiplicity_SectionThree
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.multigraded_hilbert_polynomial_top_coefficients
    (K : Type*) [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I) :
    (∀ b, 0 ≤ coeff b (homogeneousComponent
      (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I).totalDegree
      (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I))) ∧
    (∀ b : M.FactorIndex →₀ ℕ, (∃ i, M.ambientDimension i < b i) →
      coeff b (homogeneousComponent
        (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I).totalDegree
        (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I)) = 0) := by sorry
