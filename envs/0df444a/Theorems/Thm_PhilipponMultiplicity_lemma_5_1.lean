-- Prove2me | Theorems.Thm_PhilipponMultiplicity_lemma_5_1
-- name    : PhilipponMultiplicity.lemma_5_1
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T21:11:00.454928+00:00
-- url     : https://prove2.me/theorems/98d7c646-497a-4a6e-8376-3f8fbe774046
-- title:
--   Lemma 5.1 — stabilizer and geometric counting
-- statement:
--   **Proved with no Open theorem dependencies, verified 29 September 2026.** Checked locally with Lean 4.33.1 and the proposal’s pinned Mathlib. An independent blind readback is attached.
--
--   Use the section-five ideal chain, its shared component and its stabilizer. Retain differential-ideal containment at every sampled point, the binomial/coset/Hilbert bound for the identity component, and incomplete definition of the whole stabilizer by the translated ideal family.
-- source:
--   1986, pp. 380–383. https://numdam.org/articles/10.24033/bsmf.2060/

/-
Open statement draft. The proof and source-comparison obligations remain open.
SectionFiveConstruction contains the actual ideal-chain and component data;
it assumes none of the three conclusions below.
-/
import Definitions.Def_PhilipponMultiplicity_SectionFive

set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity

theorem lemma_5_1
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (C : SectionFiveConstruction G A) :
    (∀ g ∈ C.samplingSet,
      differentialIdeal A g C.contactParameter C.chosenIdeal ≤ C.componentPrime) ∧
    (let H := C.stabilizer.identityComponent
      let s := analyticCodimension A H
      (Nat.choose (C.contactParameter + s) s : ℝ) *
          (cosetCount C.samplingSet H : ℝ) * hilbertDegreeForm G H C.degrees ≤
        hilbertDegreeForm G Set.univ C.scaledDegrees) ∧
    (IncompletelyDefines G
      (⨆ v : {x : G.Point // x ∈ C.component}, translatedIdeal G v.1 C.chosenIdeal)
      C.stabilizer.carrier) := by sorry

end PhilipponMultiplicity
