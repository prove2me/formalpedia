-- Prove2me | Theorems.Thm_PhilipponMultiplicity_section_three_counterexample
-- name    : PhilipponMultiplicity.section_three_counterexample
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T21:11:15.840906+00:00
-- url     : https://prove2.me/theorems/91a0b745-b6f0-4f40-ac3a-8b974a062f7e
-- title:
--   Section 3 — printed counterexample and nonradical correction
-- statement:
--   **Compiled open theorem statement; proof not yet supplied.** Checked locally with Lean 4.33.1 and the proposal’s pinned Mathlib. An independent blind readback is attached.
--
--   Keep the exact printed three-generator ideal, its degree four, its two degree-one sections, and the isolated primary components of degrees four and two. Their degree sum is six. Contrary to the printed word “prime”, the original ideal is nonradical: the draft requires an explicit cubic witness and its square membership.
-- source:
--   1986, pp.370–371. https://numdam.org/articles/10.24033/bsmf.2060/

/-
The actual p.370–371 example. Correction: the printed three-generator I₀
is not prime and not radical, as witnessed by the explicit cubic below.
Its degree and the displayed two-component section still give 6 > 4.
-/
import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport

set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem section_three_counterexample :
    let M := BezoutBoundary.ambient
    let I₀ := BezoutBoundary.initialIdeal
    let I := BezoutBoundary.sectionIdeal
    let Q₁ := BezoutBoundary.firstComponent
    let Q₂ := BezoutBoundary.secondComponent
    let g := BezoutBoundary.nonradicalWitness
    IsMultihomogeneousIdeal M I₀ ∧ IsNontrivialIdeal M I₀ ∧
    M.IsHomogeneous BezoutBoundary.firstEquation (fun _ => 1) ∧
    M.IsHomogeneous BezoutBoundary.secondEquation (fun _ => 1) ∧
    g ∉ I₀ ∧ g ^ 2 ∈ I₀ ∧ g ∈ I₀.radical ∧ I₀.radical ≠ I₀ ∧ ¬ I₀.IsPrime ∧
    idealDimension M I₀ = 2 ∧
    Hilbert.hilbertPolynomial ℂ M.factorCount M.ambientDimension I₀ =
      BezoutBoundary.expectedInitialHilbertPolynomial ∧
    idealDegreeValue M I₀ (fun _ => 1) = 4 ∧
    I = BezoutBoundary.reducedSectionGenerators ∧ I = Q₁ ⊓ Q₂ ∧
    Q₁.IsPrimary ∧ Q₂.IsPrimary ∧ Q₁.radical ≠ Q₂.radical ∧
    I.minimalPrimes = {Q₁.radical, Q₂.radical} ∧
    Hilbert.IsRelevant ℂ M.factorCount M.ambientDimension Q₁.radical ∧
    Hilbert.IsRelevant ℂ M.factorCount M.ambientDimension Q₂.radical ∧
    idealDimension M Q₁ = 0 ∧ idealDimension M Q₂ = 0 ∧
    Hilbert.hilbertPolynomial ℂ M.factorCount M.ambientDimension Q₁ = 4 ∧
    Hilbert.hilbertPolynomial ℂ M.factorCount M.ambientDimension Q₂ = 2 ∧
    idealDegreeValue M Q₁ (fun _ => 1) = 4 ∧
    idealDegreeValue M Q₂ (fun _ => 1) = 2 ∧
    componentHilbertSum M I (⊤ : MaximalOpenLocus M) (fun _ => 1) = 6 ∧
    componentHilbertSum M I₀ (⊤ : MaximalOpenLocus M) (fun _ => 1) = 4 ∧
    componentHilbertSum M I₀ (⊤ : MaximalOpenLocus M) (fun _ => 1) <
      componentHilbertSum M I (⊤ : MaximalOpenLocus M) (fun _ => 1) ∧
    ¬ IsLocallyCohenMacaulayOn M I₀ (⊤ : MaximalOpenLocus M) := by sorry

end PhilipponMultiplicity
