-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LevelTwist_sabMapId___56b613ef0187
-- name    : P2M_GlobalTheory_LevelTwist_sabMapId___56b613ef0187
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:16:01.207494+00:00
-- url     : https://prove2.me/theorems/3d999a4b-0e33-4c37-a30b-b7ca9975730f
-- title:
--   P2 M Global Theory Level Twist sab Map Id   56b613ef0187: P2 M Global Theory Level Twist sab Map Id   56b613ef0187
-- statement:
--   The P2 M Global Theory Level Twist sab Map Id   56b613ef0187 construction uses the P2 M Global Theory Level Twist sab Map Id   56b613ef0187 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsObjTwistBySimilitude.lean#L70-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsObjTwistBySimilitude.lean#L70-L70

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsObjTwistBySimilitude
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LevelTwist
variable {X : Scheme.{0}}
variable {S : Scheme.{0}}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem P2M_GlobalTheory_LevelTwist_sabMapId___56b613ef0187 (t : SAB H S) : (sabMapId t).φ = 𝟙 _ := by sorry

alias «GlobalTheory».«LevelTwist».«sabMapId_φ» := P2M_GlobalTheory_LevelTwist_sabMapId___56b613ef0187
