-- Prove2me | Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sec_ext__7d36e2669680
-- name    : P2M_GlobalTheory_FieldBaseChange_sec_ext__7d36e2669680
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:12:30.270232+00:00
-- url     : https://prove2.me/theorems/b698f52b-d3a7-43c5-8473-3d93e7a3b30f
-- title:
--   P2 M Global Theory Field Base Change sec ext  7d36e2669680: P2 M Global Theory Field Base Change sec ext  7d36e2669680
-- statement:
--   The P2 M Global Theory Field Base Change sec ext  7d36e2669680 construction uses the P2 M Global Theory Field Base Change sec ext  7d36e2669680 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionPullOver.lean#L150-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionPullOver.lean#L150-L152

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExpF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R R' : Type} [CommRing R] [CommRing R'] {X Y Y' Z : Scheme.{0}}
variable (π : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y)
variable {π} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem P2M_GlobalTheory_FieldBaseChange_sec_ext__7d36e2669680 (hL : L.IsLB) {s s' : LB.Sec (LB.LinComb L φ ε)}
    (h : ∀ y J, Good L y J → sval s (𝟙 Y) y J = sval s' (𝟙 Y) y J) : s = s' := by sorry

alias «GlobalTheory».«FieldBaseChange».«sec_ext'» := P2M_GlobalTheory_FieldBaseChange_sec_ext__7d36e2669680
