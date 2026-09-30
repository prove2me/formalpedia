-- Prove2me | Theorems.Thm_PhilipponMultiplicity_section_three_initial_hilbert_certificate
-- name    : PhilipponMultiplicity.section_three_initial_hilbert_certificate
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-30T10:34:30.87399+00:00
-- url     : https://prove2.me/theorems/11c07ecc-1959-4db9-8120-5e015bcd9caf
-- title:
--   Section 3 counterexample: initial Hilbert polynomial and component sum
-- statement:
--   Work in the standard graded ring $R=\mathbb C[E,A,B,C,D]$, the homogeneous coordinate ring of $\mathbb P^4$, and retain the ideal printed in Philippon's Section 3:
--
--   $$I_0=(A^2C-B^2E,\ AD-BC,\ C^3-D^2E).$$
--
--   Its eventual homogeneous Hilbert polynomial is
--
--   $$H_{R/I_0}(t)=2t^2+3t+1.$$
--
--   For an ideal $J$, let $\Sigma(J)$ denote the sum of the degrees of its relevant isolated primary components, each taken canonically as the contraction of $JR_{\mathfrak p}$ for a relevant minimal prime $\mathfrak p$. Relevance means that the prime does not contain the irrelevant ideal $(E,A,B,C,D)$. The second assertion is
--
--   $$\Sigma(I_0)=4.$$
--
--   This is the initial-ideal computation needed for the degree-four versus degree-six counterexample to an unconditional component-sum inequality. The ideal here is the exact three-generator ideal, without radicalization or an additional generator. The printed assertion that it is prime is not an assumption: in fact it is nonradical, as witnessed by $AC^2-BDE$.
--
--   **Formalization Note** The Hilbert polynomial and component sum are the mission's existing canonical constructions. The component sum is evaluated at degree one on the full maximal spectrum, so every relevant minimal prime is included. These two equalities are open computational obligations; the dimension and ordinary degree follow separately from the displayed Hilbert polynomial.
-- source:
--   P. Philippon, Lemmes de zéros dans les groupes algébriques commutatifs, Bulletin de la SMF 114 (1986), pp. 370–371, explicit Section 3 counterexample. The printed ideal is retained; its printed primality assertion is corrected. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport

set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem section_three_initial_hilbert_certificate :
    let M := BezoutBoundary.ambient
    let I₀ := BezoutBoundary.initialIdeal
    Hilbert.hilbertPolynomial ℂ M.factorCount M.ambientDimension I₀ =
      BezoutBoundary.expectedInitialHilbertPolynomial ∧
    componentHilbertSum M I₀ (⊤ : MaximalOpenLocus M) (fun _ => 1) = 4 := by sorry

end PhilipponMultiplicity
