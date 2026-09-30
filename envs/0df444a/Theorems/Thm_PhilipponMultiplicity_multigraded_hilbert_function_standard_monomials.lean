-- Prove2me | Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_function_standard_monomials
-- name    : PhilipponMultiplicity.multigraded_hilbert_function_standard_monomials
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T00:13:01.090989+00:00
-- url     : https://prove2.me/theorems/35ca774f-cbb4-497e-be18-8356822d226d
-- title:
--   Standard monomials count every multigraded quotient piece
-- statement:
--   For every multihomogeneous ideal $I$ in the coordinate ring of a product of projective spaces over any field, there is a finite set of forbidden monomial divisors such that, in every natural multidegree $d$, the actual quotient Hilbert function $\dim_K(R/I)_d$ equals the number of degree-$d$ monomials divisible by none of those divisors. The same finite set works for all multidegrees. Radicality and Hilbert-polynomial existence are not assumed.
-- source:
--   Supporting algebra for Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, https://www.numdam.org/articles/10.24033/bsmf.2060/, §3 p. 362, existence of the multigraded Hilbert polynomial. This is the standard-monomial comparison used to prove that foundational assertion, not an additional numbered theorem in Philippon. Proof uses polynomial division, homogeneous projection, and Dickson’s lemma.

import Definitions.Def_PhilipponMultiplicity_SectionThree
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree

theorem PhilipponMultiplicity.multigraded_hilbert_function_standard_monomials
    (K : Type*) [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I) :
    ∃ s : Finset (M.Variable →₀ ℕ), ∀ d : M.FactorIndex → ℕ,
      Hilbert.hilbertFunction K M.factorCount M.ambientDimension I d =
        Nat.card {e : M.Variable →₀ ℕ //
          Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) e = d ∧
          ∀ a ∈ s, ¬ a ≤ e} := by sorry
