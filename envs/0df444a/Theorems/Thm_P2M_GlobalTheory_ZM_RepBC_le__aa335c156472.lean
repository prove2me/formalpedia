-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ZM_RepBC_le__aa335c156472
-- name    : P2M_GlobalTheory_ZM_RepBC_le__aa335c156472
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:19:11.442523+00:00
-- url     : https://prove2.me/theorems/3aa56623-76c5-488c-bd67-e9702247e0f9
-- title:
--   P2 M Global Theory ZM Rep BC le  aa335c156472: P2 M Global Theory ZM Rep BC le  aa335c156472
-- statement:
--   The P2 M Global Theory ZM Rep BC le  aa335c156472 construction uses the P2 M Global Theory ZM Rep BC le  aa335c156472 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ProjectiveRepresentationPullbackCoordinates.lean#L71-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ProjectiveRepresentationPullbackCoordinates.lean#L71-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ProjectiveRepresentationPullbackCoordinates
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
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.RepBC
variable {X Y Z : Scheme.{0}}

theorem P2M_GlobalTheory_ZM_RepBC_le__aa335c156472 (M : LB X) (π : Y ⟶ X) (x : Z ⟶ Y) (J : PUnit → PUnit → M.ι) :
    ((M.pull π).pull x).U J ≤ (M.pull (x ≫ π)).U (J PUnit.unit) := by sorry

alias «GlobalTheory».«ZM».«RepBC».«le₁» := P2M_GlobalTheory_ZM_RepBC_le__aa335c156472
