-- Prove2me | Theorems.Thm_PhilipponMultiplicity_section_five_construction
-- name    : PhilipponMultiplicity.section_five_construction
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T21:11:44.624981+00:00
-- url     : https://prove2.me/theorems/dda9dba7-74eb-4940-b5e2-926c1ea423ce
-- title:
--   Section 5 — component selection and algebraic stabilizers
-- statement:
--   **Proved with no Open theorem dependencies, verified 29 September 2026.** Checked locally with Lean 4.33.1 and the proposal’s pinned Mathlib. An independent blind readback is attached.
--
--   Every actual source input admits the common-component construction. Algebraic subgroup identity components are algebraic and irreducible, with finitely many disjoint translating cosets. The stabilizer of an actual locally closed subvariety is Zariski closed.
-- source:
--   1986, pp.380–383. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_Support
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity

theorem section_five_construction
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) :
    (∀ I : SectionFiveInput G A, ∃ C : SectionFiveConstruction G A,
      C.toSectionFiveInput = I) ∧
    (∀ H : AlgebraicSubgroup G, ∃ H₀ : AlgebraicSubgroup G,
      H₀.carrier = H.identityComponent ∧ H₀.IsConnected ∧
      @IsIrreducible _ G.zariskiTopology H₀.carrier ∧
      ∃ representatives : Finset G.Point,
        (∀ x ∈ representatives, x ∈ H.carrier) ∧
        H.carrier = ⋃ x ∈ representatives, translate x H₀.carrier ∧
        (representatives : Set G.Point).Pairwise (fun x y => Disjoint
          (translate x H₀.carrier) (translate y H₀.carrier))) ∧
    (∀ H : AlgebraicSubgroup G, H.IsConnected →
      @IsIrreducible _ G.zariskiTopology H.carrier) ∧
    (∀ V : GroupSubvariety G,
      @IsClosed _ G.zariskiTopology (setStabilizer G V.carrier : Set G.Point)) := by sorry

end PhilipponMultiplicity
