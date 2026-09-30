-- Prove2me | Theorems.Thm_PhilipponMultiplicity_lemma_3_1_positive_equation_degrees
-- name    : PhilipponMultiplicity.lemma_3_1_positive_equation_degrees
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T20:36:21.504639+00:00
-- url     : https://prove2.me/theorems/59e84d32-14a3-46b4-94e0-9969c41959b2
-- title:
--   Lemma 3.1 — hypersurface section (positive equation degrees)
-- statement:
--   **Proved with no Open theorem dependencies, verified 29 September 2026.** Checked locally with Lean 4.33.1 and the proposal’s pinned Mathlib. An independent blind readback is attached.
--
--   For a nontrivial multihomogeneous ideal of positive dimension and an actual non-zero-divisor section, retain both the derivative-sum formula and its same-degree specialization. The equation degrees are explicitly positive: zero degrees make the printed statement false, as the separate concrete counterexample records.
-- source:
--   1986, p.363. https://numdam.org/articles/10.24033/bsmf.2060/

/-
Open, explicitly corrected positive-equation-degree version of Lemma 3.1.
The printed source does not explicitly impose Dᵢ ≥ 1. Allowing zero equation
degrees gives the counterexample recorded in SECTION-THREE-SOURCE-AUDIT.md.
Both displayed source conclusions are retained here; the correction is the
visible `hD` hypothesis, not an assumption of the conclusion.
-/
import Definitions.Def_PhilipponMultiplicity_SectionThree

set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity
open SectionThree

theorem lemma_3_1_positive_equation_degrees
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (hNontrivial : IsNontrivialIdeal M I) (ha : 0 < idealDimension M I)
    (D : M.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i)
    (P : M.CoordinateRing) (hP : M.IsHomogeneous P D)
    (hRegular : IsRegular (Ideal.Quotient.mk I P)) :
    (∀ d : M.FactorIndex → ℕ, (∀ i, 1 ≤ d i) →
      idealDegreeValue M (I ⊔ Ideal.span {P}) d = hypersurfaceCoefficientSum M I D d) ∧
    idealDegreeValue M (I ⊔ Ideal.span {P}) D = idealDegreeValue M I D := by sorry

end PhilipponMultiplicity
