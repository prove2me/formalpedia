-- Prove2me | Theorems.Thm_PhilipponMultiplicity_Hilbert_relevantCore_krull_dimension
-- name    : PhilipponMultiplicity.Hilbert.relevantCore_krull_dimension
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T02:39:25.058198+00:00
-- url     : https://prove2.me/theorems/0ae1bc93-4efe-41a7-ade5-54b2b1ff2546
-- title:
--   Hilbert dimension and the Krull dimension of the relevant cone
-- statement:
--   For a nontrivial multihomogeneous ideal $I$ in $p$ projective blocks, intersect its actual relevant minimal primes to form the reduced relevant cone. Its quotient ring has Krull dimension equal to the total degree of the actual multigraded Hilbert polynomial plus $p$. Irrelevant components are removed before making this comparison.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, §3, printed pp. 361–363, https://www.numdam.org/articles/10.24033/bsmf.2060/. A granular supporting assertion for the original Section 3 statements; definitions are unchanged.

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.Hilbert.relevantCore_krull_dimension
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (hNontrivial : IsNontrivialIdeal M I) :
    ringKrullDim (M.CoordinateRing ⧸ relevantRadicalCore M I) =
      ((idealDimension M I + M.factorCount : ℕ) : WithBot ℕ∞) := by sorry
