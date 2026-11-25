-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CubeLift_pt_p__5876b0f23257
-- name    : P2M_GlobalTheory_CubeLift_pt_p__5876b0f23257
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:00:05.033796+00:00
-- url     : https://prove2.me/theorems/6bdfa490-b4f0-4a45-9f1e-99aaf5e7f04e
-- title:
--   P2 M Global Theory Cube Lift pt p  5876b0f23257: P2 M Global Theory Cube Lift pt p  5876b0f23257
-- statement:
--   The P2 M Global Theory Cube Lift pt p  5876b0f23257 construction uses the P2 M Global Theory Cube Lift pt p  5876b0f23257 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EvSurjective.lean#L122-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EvSurjective.lean#L122-L125

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EvSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.CubeLift
open SplitTorus (ev univPt ptOf pull bcMap ofVal valHom)
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (chi torusFst)
variable {S : Scheme.{0}} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {Z Z' V : Over S}

theorem P2M_GlobalTheory_CubeLift_pt_p__5876b0f23257 (x y u : Z ⟶ splitTorus S X) : pt x y u ≫ SplitTorus.torusMap S p₂ = y := by sorry

alias «GlobalTheory».«CubeLift».«pt_p₂» := P2M_GlobalTheory_CubeLift_pt_p__5876b0f23257
