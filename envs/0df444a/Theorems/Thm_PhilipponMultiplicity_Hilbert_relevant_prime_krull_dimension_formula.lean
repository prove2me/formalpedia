-- Prove2me | Theorems.Thm_PhilipponMultiplicity_Hilbert_relevant_prime_krull_dimension_formula
-- name    : PhilipponMultiplicity.Hilbert.relevant_prime_krull_dimension_formula
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-27T07:02:24.73413+00:00
-- url     : https://prove2.me/theorems/fc3e934a-e98f-42c1-92f2-5aad2f0b78aa
-- title:
--   Hilbert–Krull comparison for a relevant multihomogeneous prime
-- statement:
--   Let $q$ be a relevant multihomogeneous prime in the coordinate ring $R$ of a product of $s$ projective spaces over any field. Then
--   $$\dim(R/q)=\deg F_q+s,$$
--   where $F_q$ is the actual eventual multigraded Hilbert polynomial. This is the explicit remaining prime-case geometric foundation. It does not assume the equality or redefine either dimension.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, §3, printed pp. 362–364; https://www.numdam.org/articles/10.24033/bsmf.2060/ . The multigraded Hilbert-dimension identification, with the affine cone contributing one dimension per projective block. The single-graded analogue is Stacks Project, Lemma 10.117.1, https://stacks.math.columbia.edu/tag/00P5 . The multigraded prime comparison is not yet proved in this contribution.

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.Hilbert.relevant_prime_krull_dimension_formula
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (q : Ideal M.CoordinateRing) (hq : q.IsPrime)
    (hhom : IsMultihomogeneousIdeal M q)
    (hrel : IsRelevant K M.factorCount M.ambientDimension q) :
    ringKrullDim (M.CoordinateRing ⧸ q) =
      ((idealDimension M q + M.factorCount : ℕ) : WithBot ℕ∞) := by sorry
