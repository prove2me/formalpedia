-- Prove2me | Theorems.Thm_PhilipponMultiplicity_Hilbert_degreeValue_antitone_of_dimension_eq
-- name    : PhilipponMultiplicity.Hilbert.degreeValue_antitone_of_dimension_eq
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T02:38:54.459708+00:00
-- url     : https://prove2.me/theorems/409c29b3-7ca9-464a-a3e3-7e610362b851
-- title:
--   Equal-dimensional inclusion decreases the normalized Hilbert degree
-- statement:
--   For multihomogeneous ideals $I\subseteq J$ over a field, assume their actual Hilbert polynomials have the same total degree. At every natural multidegree $d$, $$\mathcal H(J;d)\le\mathcal H(I;d).$$ The statement includes dimension zero and zero evaluation coordinates.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, comparison after Lemma 3.2, printed p. 364; used on p. 370, https://www.numdam.org/articles/10.24033/bsmf.2060/. A granular supporting assertion for the original Section 3 statements; definitions are unchanged.

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.Hilbert.degreeValue_antitone_of_dimension_eq
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (I J : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hJ : IsMultihomogeneousIdeal M J)
    (hle : I ≤ J) (hdim : idealDimension M I = idealDimension M J)
    (d : M.FactorIndex → ℕ) : idealDegreeValue M J d ≤ idealDegreeValue M I d := by sorry
