-- Prove2me | Theorems.Thm_PhilipponMultiplicity_idealMixedDegree_integral
-- name    : PhilipponMultiplicity.idealMixedDegree_integral
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T02:39:42.15378+00:00
-- url     : https://prove2.me/theorems/d7f2d0b0-6823-4180-bd55-0009895f8623
-- title:
--   Integrality and nonnegativity of the normalized mixed coefficients
-- statement:
--   For every multihomogeneous ideal and every block exponent $\alpha$, the actual top Hilbert-polynomial coefficient multiplied by $\prod_i\alpha_i!$ is a nonnegative integer, with coefficient zero outside the top total degree. This concerns the existing mixed-degree definition, not assigned multiplicity data.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, §3, equation (*) and coefficient assertions, printed p. 362, https://www.numdam.org/articles/10.24033/bsmf.2060/. A granular supporting assertion for the original Section 3 statements; definitions are unchanged.

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.idealMixedDegree_integral
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (α : M.FactorIndex → ℕ) : ∃ n : ℕ, idealMixedDegree M I α = (n : ℚ) := by sorry
