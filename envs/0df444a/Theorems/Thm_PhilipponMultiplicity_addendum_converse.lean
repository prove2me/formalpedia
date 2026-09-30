-- Prove2me | Theorems.Thm_PhilipponMultiplicity_addendum_converse
-- name    : PhilipponMultiplicity.addendum_converse
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-23T21:10:56.752072+00:00
-- url     : https://prove2.me/theorems/c86d0506-9d9d-4203-8b03-416dd74a15e2
-- title:
--   1987 addendum — converse construction (positive dimension)
-- statement:
--   **Compiled open theorem statement; proof not yet supplied.** Checked locally with Lean 4.33.1 and the proposal’s pinned Mathlib. An independent blind readback is attached.
--
--   For an ambient group of positive dimension, given the source degree lower bounds and a subgroup satisfying the Hilbert inequality with reciprocal constant 4^n n!, construct a polynomial of the specified multidegree with contact at least T+1 on every sampled subgroup translate, but not identically zero on G. The n=0 obstruction is explicitly recorded as a separate required counterexample; this positive-dimension correction is not presented as a verbatim hypothesis from the printed statement.
-- source:
--   1987, p. 398. https://numdam.org/articles/10.24033/bsmf.2084/

/-
Open statement draft. The proof and source-comparison obligations remain open.
This draft explicitly restricts the ambient group to positive dimension.
-/
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_Analytic

set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity

theorem addendum_converse
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (hn : 0 < G.dimension) (A : AnalyticSubgroup G)
    (sample : Finset G.Point) (hsample : 0 ∈ sample) (T : ℕ) (D : G.FactorIndex → ℕ)
    (hD : ∀ i, hilbertDegreeForm G Set.univ (fun _ => 1) ≤ (D i : ℝ))
    (H : AlgebraicSubgroup G)
    (hbound :
      (Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier) : ℝ) *
          (cosetCount sample H.carrier : ℝ) * hilbertDegreeForm G H.carrier D ≤
        (1 / ((4 : ℝ) ^ G.dimension * (G.dimension.factorial : ℝ))) *
          hilbertDegreeForm G Set.univ D) :
    ∃ P : G.CoordinateRing,
      P ≠ 0 ∧ IsMultihomogeneousOfDegree G P D ∧
      (∀ g ∈ sample, ∀ h ∈ H.carrier,
        ((T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P (g + h)) ∧
      (∃ x : G.Point, x ∉ zeroLocusOnGroup G P) := by sorry

end PhilipponMultiplicity
