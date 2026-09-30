-- Prove2me | Theorems.Thm_PhilipponMultiplicity_Hilbert_cumulativeHilbertFunction_polynomial_bounds
-- name    : PhilipponMultiplicity.Hilbert.cumulativeHilbertFunction_polynomial_bounds
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-27T07:44:05.322451+00:00
-- url     : https://prove2.me/theorems/d02cee73-8026-439e-b99e-a777665b1ecf
-- title:
--   Matching polynomial growth bounds for the actual quotient filtration
-- statement:
--   Let $q$ be a relevant multihomogeneous prime, $a$ the total degree of its actual Hilbert polynomial, and $s$ the number of projective blocks. There exist positive rational constants $c,C$ and a natural threshold $N$ such that for every $n\ge N$, $$c n^{a+s}\le C_q(2sn),\qquad C_q(n)\le C(n+1)^{a+s},$$ where $C_q$ is the actual vector-space dimension of the total-degree filtration in $R/q$. These bounds prove the Hilbert-polynomial side of the growth comparison; they do not assume or assert the remaining equality with Krull dimension.
-- source:
--   Supporting formalization for Philippon (1986), §3, printed pp. 362–364, https://www.numdam.org/articles/10.24033/bsmf.2060/ . Matching polynomial growth bounds for the actual quotient filtration.

import Definitions.Def_PhilipponMultiplicity_HilbertGrowth
set_option autoImplicit false
open scoped BigOperators Topology
open Filter
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.Hilbert.cumulativeHilbertFunction_polynomial_bounds
{K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (Q : Ideal M.CoordinateRing) (hQ : Q.IsPrime)
    (hhom : IsMultihomogeneousIdeal M Q)
    (hrel : IsRelevant K M.factorCount M.ambientDimension Q) :
    ∃ c C : ℚ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      c * (n : ℚ) ^ (SectionThree.idealDimension M Q + M.factorCount) ≤
          (cumulativeHilbertFunction M Q (2 * M.factorCount * n) : ℚ) ∧
        (cumulativeHilbertFunction M Q n : ℚ) ≤
          C * ((n + 1 : ℕ) : ℚ) ^ (SectionThree.idealDimension M Q + M.factorCount) := by sorry
