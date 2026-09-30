-- Prove2me | Theorems.Thm_PhilipponMultiplicity_Hilbert_primaryComponent_degreeValue_eq_localLength
-- name    : PhilipponMultiplicity.Hilbert.primaryComponent_degreeValue_eq_localLength
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T23:12:09.762263+00:00
-- url     : https://prove2.me/theorems/629d3422-0eae-4dd8-8399-ac699743801b
-- title:
--   Canonical component degree equals generic multiplicity times support degree
-- statement:
--   Let $I$ be a multihomogeneous ideal over any field and let $q$ be a relevant minimal prime. Its canonical isolated primary component $Q_q(I)=IR_q\cap R$ satisfies, at every natural degree vector $d$,
--   $$H(Q_q(I);d)=\operatorname{length}_{R_q}(R_q/IR_q)\,H(q;d).$$
--   Thus the existing canonical-component degree and the actual generic multiplicity agree, without redefining either quantity. Zero degree entries are allowed.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs. Section 3, printed pp. 364–365: the degree of an isolated primary component and its generic length, used in the component-sum definition and Proposition 3.3. https://www.numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.Hilbert.primaryComponent_degreeValue_eq_localLength
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
(I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (q : PrimeSpectrum M.CoordinateRing)
    (hq : q.asIdeal ∈ I.minimalPrimes)
    (hrel : IsRelevant K M.factorCount M.ambientDimension q.asIdeal)
    (d : M.FactorIndex → ℕ) :
    idealDegreeValue M (primaryComponent K M.factorCount M.ambientDimension I q) d =
      ((localLength K M.factorCount M.ambientDimension I q).toNat : ℚ) *
        idealDegreeValue M q.asIdeal d := by sorry
