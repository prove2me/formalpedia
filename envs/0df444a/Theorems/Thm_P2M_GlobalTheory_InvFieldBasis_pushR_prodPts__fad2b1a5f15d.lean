-- Prove2me | Theorems.Thm_P2M_GlobalTheory_InvFieldBasis_pushR_prodPts__fad2b1a5f15d
-- name    : P2M_GlobalTheory_InvFieldBasis_pushR_prodPts__fad2b1a5f15d
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:09:18.089198+00:00
-- url     : https://prove2.me/theorems/7b03e617-dfb7-4410-97e8-ebf84875619a
-- title:
--   P2 M Global Theory Inv Field Basis push R prod Pts  fad2b1a5f15d: P2 M Global Theory Inv Field Basis push R prod Pts  fad2b1a5f15d
-- statement:
--   The P2 M Global Theory Inv Field Basis push R prod Pts  fad2b1a5f15d construction uses the P2 M Global Theory Inv Field Basis push R prod Pts  fad2b1a5f15d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PreimageTranslate.lean#L31-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PreimageTranslate.lean#L31-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningFieldStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PreimageTranslate
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS GlobalTheory.TangentOrigin GlobalTheory.SqZero GlobalTheory.LieBaseChange
open ReciprocityTheory.ChartRestriction.G.Chart (sp fstD pushR pullR fB)
open TrivSqZeroExt (inl inr)
noncomputable section
open GlobalTheory GlobalTheory.InvFieldBasis
variable {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] {n : ℕ}
variable {C : Type} [CommRing C] [Algebra K C]

theorem P2M_GlobalTheory_InvFieldBasis_pushR_prodPts__fad2b1a5f15d (v : Fin n → (epsR K ⟶ G)) (c : Fin n → C) :
    pushR G (Chart.prodPts c (bcVec C v)) =
      expPt v (fun i => (inr (c i) : DualNumber C)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) := by sorry

alias «GlobalTheory».«InvFieldBasis».«pushR_prodPts'» := P2M_GlobalTheory_InvFieldBasis_pushR_prodPts__fad2b1a5f15d
