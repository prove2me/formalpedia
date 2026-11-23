-- Prove2me | Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_gs_zero__47fb152d3439
-- name    : P2M_GlobalTheory_FieldBaseChange_gs_zero__47fb152d3439
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:16:46.78086+00:00
-- url     : https://prove2.me/theorems/55058ff0-4c3f-44c4-ad01-6c1785c6c22f
-- title:
--   P2 M Global Theory Field Base Change gs zero  47fb152d3439: P2 M Global Theory Field Base Change gs zero  47fb152d3439
-- statement:
--   The P2 M Global Theory Field Base Change gs zero  47fb152d3439 construction uses the P2 M Global Theory Field Base Change gs zero  47fb152d3439 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionPullOver.lean#L42-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionPullOver.lean#L42-L43

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

theorem P2M_GlobalTheory_FieldBaseChange_gs_zero__47fb152d3439 (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) : gs r z U 0 = 0 := by sorry

alias «GlobalTheory».«FieldBaseChange».«gs_zero'» := P2M_GlobalTheory_FieldBaseChange_gs_zero__47fb152d3439
