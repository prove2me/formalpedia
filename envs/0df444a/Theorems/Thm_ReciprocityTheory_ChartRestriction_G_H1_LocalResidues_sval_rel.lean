-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_LocalResidues_sval_rel
-- name    : ReciprocityTheory.ChartRestriction.G.H1.LocalResidues.sval_rel
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:27:59.83994+00:00
-- url     : https://prove2.me/theorems/8edf60a4-88d3-402a-bd2a-d47547d8004f
-- title:
--   Local Residues: sval rel
-- statement:
--   The Local Residues construction uses the sval rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/LocalResidues.lean#L56-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/LocalResidues.lean#L56-L68

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_JetApproximation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_LocalResidues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.LocalResidues
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {k : Type} [Field k] {X W Z : Scheme.{0}}

theorem ReciprocityTheory.ChartRestriction.G.H1.LocalResidues.sval_rel {L : LB X} {K : Type} [Fintype K] {φ : K → (W ⟶ X)} {ε : K → ℤ}
    (s s₀ : LB.Sec (LB.LinComb L φ ε)) (D : W.Opens) (rr : Γ(W, D))
    (hrel : ∀ j, (W.presheaf.map (homOfLE (inf_le_right : D ⊓ (LB.LinComb L φ ε).U j ≤ (LB.LinComb L φ ε).U j)).op).hom
        (s.f j) =
      (W.presheaf.map (homOfLE (inf_le_left : D ⊓ (LB.LinComb L φ ε).U j ≤ D)).op).hom rr *
      (W.presheaf.map (homOfLE (inf_le_right : D ⊓ (LB.LinComb L φ ε).U j ≤ (LB.LinComb L φ ε).U j)).op).hom
        (s₀.f j))
    (r : Z ⟶ W) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (hz : r z ∈ D) :
    sval s r z J = gs r z D rr * sval s₀ r z J := by sorry
