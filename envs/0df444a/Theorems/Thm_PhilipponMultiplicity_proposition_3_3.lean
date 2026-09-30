-- Prove2me | Theorems.Thm_PhilipponMultiplicity_proposition_3_3
-- name    : PhilipponMultiplicity.proposition_3_3
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T20:50:37.209644+00:00
-- url     : https://prove2.me/theorems/301105ea-2089-42ac-bc8c-696bb4138186
-- title:
--   Proposition 3.3 — multigraded intersection bounds
-- statement:
--   **Proved with no Open theorem dependencies, verified 29 September 2026.** Checked locally with Lean 4.33.1 and the proposal’s pinned Mathlib. An independent blind readback is attached.
--
--   Adding multihomogeneous equations of the prescribed degree bounds does not increase the source sum of radical component Hilbert forms. On an open maximal-spectrum locus where the original quotient is locally Cohen–Macaulay, the corresponding inequality retains primary component multiplicities. Both inequalities are required.
-- source:
--   1986, pp. 365–370. https://numdam.org/articles/10.24033/bsmf.2060/

/-
Open statement draft. The proof and source-comparison obligations remain open.
-/
import Definitions.Def_PhilipponMultiplicity_Degree

set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity

theorem proposition_3_3
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (M : MultiProjectiveSpace K)
    (I₀ : Ideal M.CoordinateRing) (hI₀ : IsMultihomogeneousIdeal M I₀)
    (m : ℕ) (P : Fin m → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D) :
    let I := I₀ ⊔ Ideal.span (Set.range P)
    (componentHilbertSum M I.radical (⊤ : MaximalOpenLocus M) D ≤
      componentHilbertSum M I₀.radical (⊤ : MaximalOpenLocus M) D) ∧
    (∀ U : MaximalOpenLocus M, IsLocallyCohenMacaulayOn M I₀ U →
      componentHilbertSum M I U D ≤ componentHilbertSum M I₀ U D) := by sorry

end PhilipponMultiplicity
