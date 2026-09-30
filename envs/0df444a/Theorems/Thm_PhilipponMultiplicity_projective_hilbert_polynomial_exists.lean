-- Prove2me | Theorems.Thm_PhilipponMultiplicity_projective_hilbert_polynomial_exists
-- name    : PhilipponMultiplicity.projective_hilbert_polynomial_exists
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-25T18:18:44.234804+00:00
-- url     : https://prove2.me/theorems/5a20ecb5-5da7-4c19-9b56-1963b293babf
-- title:
--   Existence of the ordinary projective Hilbert polynomial
-- statement:
--   Let $V$ be a locally closed subset of $\mathbf P^N$ over a field. Its homogeneous coordinate-ring quotient has an eventual Hilbert polynomial with rational coefficients: there are a polynomial $P$ and a bound $n_0$ such that
--   $$
--   P(n)=\dim_K(R/I(V))_n\qquad(n\ge n_0).
--   $$
--   The quotient degree piece and eventual-agreement predicate are the mission's original definitions. Empty subsets are included. This is the single-projective-factor case of the Hilbert-polynomial existence foundation in §3; it does not assume a degree formula or a prescribed Hilbert polynomial.
-- source:
--   Philippon, Lemmes de zéros dans les groupes algébriques commutatifs (1986), https://numdam.org/articles/10.24033/bsmf.2060/, §3 pp. 361–362 and Lemma 3.4 p. 371. Supporting algebra for the numbered result; the paper itself uses the geometric interpretation of the mixed coefficients.

import Definitions.Def_PhilipponMultiplicity_SectionThree

set_option autoImplicit false
open scoped BigOperators
open PhilipponMultiplicity PhilipponMultiplicity.SectionThree

theorem PhilipponMultiplicity.projective_hilbert_polynomial_exists
    (K : Type*) [Field K] (N : ℕ) (V : ProjectiveSubvariety K N) :
    ∃ P, Hilbert.IsHilbertPolynomial K 1 (fun _ => N)
      ((projectiveSpace K N).vanishingIdeal V.carrierInSingleFactor) P := by sorry
