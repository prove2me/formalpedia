-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ZM_RepBC_le__8683792fd0d2
-- name    : P2M_GlobalTheory_ZM_RepBC_le__8683792fd0d2
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:26:01.53595+00:00
-- url     : https://prove2.me/theorems/36eefae1-2193-58d2-a63b-f8e31e690b7e
-- title:
--   P2 M Global Theory ZM Rep BC le  8683792fd0d2: P2 M Global Theory ZM Rep BC le  8683792fd0d2
-- statement:
--   The P2 M Global Theory ZM Rep BC le  8683792fd0d2 construction uses the P2 M Global Theory ZM Rep BC le  8683792fd0d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ProjectiveRepresentationPullbackCoordinates.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ProjectiveRepresentationPullbackCoordinates.lean#L75-L77

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

theorem P2M_GlobalTheory_ZM_RepBC_le__8683792fd0d2 (M : LB X) (π : Y ⟶ X) (x : Z ⟶ Y) (j : PUnit → M.ι) :
    (M.pull (x ≫ π)).U j ≤ ((M.pull π).pull x).U (fun _ => j) := by sorry

alias «GlobalTheory».«ZM».«RepBC».«le₂» := P2M_GlobalTheory_ZM_RepBC_le__8683792fd0d2
