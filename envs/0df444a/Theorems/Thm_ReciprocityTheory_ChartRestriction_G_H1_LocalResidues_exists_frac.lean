-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_LocalResidues_exists_frac
-- name    : ReciprocityTheory.ChartRestriction.G.H1.LocalResidues.exists_frac
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:28:19.137091+00:00
-- url     : https://prove2.me/theorems/c7756abc-92bd-49a6-9a7a-45b635c2340d
-- title:
--   Local Residues: exists frac
-- statement:
--   The Local Residues construction uses the exists frac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/LocalResidues.lean#L21-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/LocalResidues.lean#L21-L36

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

theorem ReciprocityTheory.ChartRestriction.G.H1.LocalResidues.exists_frac (h0 : X ⟶ W) [IsIso h0] (D : W.Opens) (hD : IsAffineOpen D) (y : X) (hy : h0 y ∈ D)
    (f : X.presheaf.stalk y) :
    ∃ g g' : Γ(W, D), IsUnit (gs h0 y D g') ∧ f * gs h0 y D g' = gs h0 y D g := by sorry
