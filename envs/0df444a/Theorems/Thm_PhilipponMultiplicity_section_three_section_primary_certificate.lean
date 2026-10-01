-- Prove2me | Theorems.Thm_PhilipponMultiplicity_section_three_section_primary_certificate
-- name    : PhilipponMultiplicity.section_three_section_primary_certificate
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-30T10:34:49.903237+00:00
-- url     : https://prove2.me/theorems/b26f02f7-930c-4639-8113-00af2b88aeab
-- title:
--   Section 3 counterexample: section primary components and Hilbert polynomials
-- statement:
--   Work in $R=\mathbb C[E,A,B,C,D]$ with its standard grading. Set
--
--   $$I_0=(A^2C-B^2E,\ AD-BC,\ C^3-D^2E),\qquad I=I_0+(C,A-D),$$
--
--   and define
--
--   $$Q_1=(A^2,B^2,C,A-D),\qquad Q_2=(E,A^2,C,A-D).$$
--
--   Then $Q_1$ and $Q_2$ are primary with distinct radicals, and
--
--   $$I=Q_1\cap Q_2,\qquad \operatorname{Min}(I)=\{\sqrt{Q_1},\sqrt{Q_2}\}.$$
--
--   Both radicals are relevant: neither contains the irrelevant ideal $(E,A,B,C,D)$. The eventual homogeneous Hilbert polynomials of the two components are
--
--   $$H_{R/Q_1}(t)=4,\qquad H_{R/Q_2}(t)=2.$$
--
--   Finally, the sum of the degrees of the canonical relevant isolated primary components of $I$ is
--
--   $$\Sigma(I)=6.$$
--
--   This records the primary-component and Hilbert computations for the two linear sections in Philippon's Section 3 counterexample. All ideals are fixed explicitly; in particular the initial ideal is the printed three-generator ideal, with no primality assumption.
--
--   **Formalization Note** The component sum uses contractions from localization at the actual minimal primes and is evaluated at degree one on the full maximal spectrum. The component dimensions and degree values are derived separately from the constant Hilbert polynomials.
-- source:
--   P. Philippon, Lemmes de zéros dans les groupes algébriques commutatifs, Bulletin de la SMF 114 (1986), pp. 370–371, explicit Section 3 counterexample. The printed ideal is retained; its printed primality assertion is corrected. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport

set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem section_three_section_primary_certificate :
    let M := BezoutBoundary.ambient
    let I := BezoutBoundary.sectionIdeal
    let Q₁ := BezoutBoundary.firstComponent
    let Q₂ := BezoutBoundary.secondComponent
    I = Q₁ ⊓ Q₂ ∧ Q₁.IsPrimary ∧ Q₂.IsPrimary ∧ Q₁.radical ≠ Q₂.radical ∧
    I.minimalPrimes = {Q₁.radical, Q₂.radical} ∧
    Hilbert.IsRelevant ℂ M.factorCount M.ambientDimension Q₁.radical ∧
    Hilbert.IsRelevant ℂ M.factorCount M.ambientDimension Q₂.radical ∧
    Hilbert.hilbertPolynomial ℂ M.factorCount M.ambientDimension Q₁ = 4 ∧
    Hilbert.hilbertPolynomial ℂ M.factorCount M.ambientDimension Q₂ = 2 ∧
    componentHilbertSum M I (⊤ : MaximalOpenLocus M) (fun _ => 1) = 6 := by sorry

end PhilipponMultiplicity
