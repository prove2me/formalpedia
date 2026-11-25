-- Prove2me | Theorems.Thm_P2M_GlobalTheory_PointQuot_openLE___050aa5dd460f
-- name    : P2M_GlobalTheory_PointQuot_openLE___050aa5dd460f
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:58.800929+00:00
-- url     : https://prove2.me/theorems/3bff0312-8755-4dbf-9941-35f53f0b4799
-- title:
--   P2 M Global Theory Point Quot open LE   050aa5dd460f: P2 M Global Theory Point Quot open LE   050aa5dd460f
-- statement:
--   The P2 M Global Theory Point Quot open LE   050aa5dd460f construction uses the P2 M Global Theory Point Quot open LE   050aa5dd460f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsQuotientByFiniteGroupOfPoints.lean#L60-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsQuotientByFiniteGroupOfPoints.lean#L60-L62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsQuotientByFiniteGroupOfPoints
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
open GlobalTheory
open GlobalTheory.PointQuot
variable {S : Scheme.{0}}

theorem P2M_GlobalTheory_PointQuot_openLE___050aa5dd460f (Z : Over S) {V W : Z.left.Opens} (h : V ≤ W) :
    openLE Z h ≫ openι Z W = openι Z V := by sorry

alias «GlobalTheory».«PointQuot».«openLE_ι» := P2M_GlobalTheory_PointQuot_openLE___050aa5dd460f
