-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CubeLift_pt_p__b32ea6907c6f
-- name    : P2M_GlobalTheory_CubeLift_pt_p__b32ea6907c6f
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:59:07.493498+00:00
-- url     : https://prove2.me/theorems/f37d1222-b563-4451-a8ae-ffdec5646ddc
-- title:
--   P2 M Global Theory Cube Lift pt p  b32ea6907c6f: P2 M Global Theory Cube Lift pt p  b32ea6907c6f
-- statement:
--   The P2 M Global Theory Cube Lift pt p  b32ea6907c6f construction uses the P2 M Global Theory Cube Lift pt p  b32ea6907c6f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EvSurjective.lean#L117-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EvSurjective.lean#L117-L120

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

theorem P2M_GlobalTheory_CubeLift_pt_p__b32ea6907c6f (x y u : Z ⟶ splitTorus S X) : pt x y u ≫ SplitTorus.torusMap S p₁ = x := by sorry

alias «GlobalTheory».«CubeLift».«pt_p₁» := P2M_GlobalTheory_CubeLift_pt_p__b32ea6907c6f
