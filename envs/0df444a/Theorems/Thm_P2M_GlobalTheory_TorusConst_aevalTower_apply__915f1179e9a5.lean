-- Prove2me | Theorems.Thm_P2M_GlobalTheory_TorusConst_aevalTower_apply__915f1179e9a5
-- name    : P2M_GlobalTheory_TorusConst_aevalTower_apply__915f1179e9a5
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:08:09.5381+00:00
-- url     : https://prove2.me/theorems/6660b96a-fda7-4414-a4a4-bb5cedc3693d
-- title:
--   P2 M Global Theory Torus Const aeval Tower apply  915f1179e9a5: P2 M Global Theory Torus Const aeval Tower apply  915f1179e9a5
-- statement:
--   The P2 M Global Theory Torus Const aeval Tower apply  915f1179e9a5 construction uses the P2 M Global Theory Torus Const aeval Tower apply  915f1179e9a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusToAbelianVarietyConst.lean#L152-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusToAbelianVarietyConst.lean#L152-L153

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.TorusConst
open Polynomial TorusToProper
variable {K : Type} [Field K] {B : Over (Spec (CommRingCat.of K))}

theorem P2M_GlobalTheory_TorusConst_aevalTower_apply__915f1179e9a5 {R A : Type} [CommRing R] [Algebra K R] [CommRing A] [Algebra K A]
    (c : R →ₐ[K] A) (x : A) (a : R[X]) : aevalTower c x a = eval₂ (c : R →+* A) x a := by sorry

alias «GlobalTheory».«TorusConst».«aevalTower_apply'» := P2M_GlobalTheory_TorusConst_aevalTower_apply__915f1179e9a5
