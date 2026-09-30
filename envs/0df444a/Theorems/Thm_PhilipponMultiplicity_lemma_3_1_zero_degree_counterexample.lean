-- Prove2me | Theorems.Thm_PhilipponMultiplicity_lemma_3_1_zero_degree_counterexample
-- name    : PhilipponMultiplicity.lemma_3_1_zero_degree_counterexample
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T21:11:58.094097+00:00
-- url     : https://prove2.me/theorems/ccf7957e-8d89-4a8b-ad84-4d65c3aaacc8
-- title:
--   Lemma 3.1 — concrete zero-degree counterexample
-- statement:
--   **Compiled open theorem statement; proof not yet supplied.** Checked locally with Lean 4.33.1 and the proposal’s pinned Mathlib. An independent blind readback is attached.
--
--   In complex P²×P¹ take I=(Y₁X₁,Y₁X₂), P=Y₀ of bidegree (0,1). Require the actual quotient regularity, primary intersection and Hilbert polynomials, showing both printed equalities fail without the positive-degree convention.
-- source:
--   1986, p.363; source-boundary correction. https://numdam.org/articles/10.24033/bsmf.2060/

/-
Concrete open counterexample to the unrestricted-zero-degree reading of
printed Lemma 3.1. Every ideal, polynomial and degree is explicitly fixed.
This is separate from the corrected positive-degree source theorem.
-/
import Definitions.Def_PhilipponMultiplicity_SectionThree

set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity
open SectionThree

theorem lemma_3_1_zero_degree_counterexample :
    let M := ZeroDegreeBoundary.ambient
    let I := ZeroDegreeBoundary.ideal
    let P := ZeroDegreeBoundary.polynomial
    let D := ZeroDegreeBoundary.equationDegrees
    let J := I ⊔ Ideal.span {P}
    I = Ideal.span {ZeroDegreeBoundary.secondCoordinate 1} ⊓
      Ideal.span {ZeroDegreeBoundary.firstCoordinate 1, ZeroDegreeBoundary.firstCoordinate 2} ∧
    IsMultihomogeneousIdeal M I ∧ IsNontrivialIdeal M I ∧
    M.IsHomogeneous P D ∧ IsRegular (Ideal.Quotient.mk I P) ∧
    idealDimension M I = 2 ∧
    Hilbert.hilbertPolynomial ℂ M.factorCount M.ambientDimension I =
      ZeroDegreeBoundary.expectedHilbertPolynomial ∧
    Hilbert.hilbertPolynomial ℂ M.factorCount M.ambientDimension J = 1 ∧
    (∀ d : M.FactorIndex → ℕ, idealDegreeValue M I d = (d (0 : Fin 2) : ℚ) ^ 2) ∧
    (∀ d : M.FactorIndex → ℕ, idealDegreeValue M J d = 1) ∧
    hypersurfaceCoefficientSum M I D (fun _ => 1) = 0 ∧
    idealDegreeValue M J (fun _ => 1) ≠ hypersurfaceCoefficientSum M I D (fun _ => 1) ∧
    idealDegreeValue M J D ≠ idealDegreeValue M I D := by sorry

end PhilipponMultiplicity
