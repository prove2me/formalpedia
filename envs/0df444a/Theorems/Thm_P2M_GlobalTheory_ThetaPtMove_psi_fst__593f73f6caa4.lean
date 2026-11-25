-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ThetaPtMove_psi_fst__593f73f6caa4
-- name    : P2M_GlobalTheory_ThetaPtMove_psi_fst__593f73f6caa4
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:35:55.632579+00:00
-- url     : https://prove2.me/theorems/707ea17b-05cb-58c3-9ddd-6fecfb6dadb4
-- title:
--   P2 M Global Theory Theta Pt Move psi fst  593f73f6caa4: P2 M Global Theory Theta Pt Move psi fst  593f73f6caa4
-- statement:
--   The P2 M Global Theory Theta Pt Move psi fst  593f73f6caa4 construction uses the P2 M Global Theory Theta Pt Move psi fst  593f73f6caa4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/IsThetaPtOverMove.lean#L65-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/IsThetaPtOverMove.lean#L65-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaPtMove
open GlobalTheory.CommPairing GlobalTheory.ConstFam GlobalTheory.GlobalLift
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)

theorem P2M_GlobalTheory_ThetaPtMove_psi_fst__593f73f6caa4 : psi hp τ hτ ≫ (fst T₀ G).left = (fst T A).left ≫ τ := by sorry

alias «GlobalTheory».«ThetaPtMove».«psi_fst'» := P2M_GlobalTheory_ThetaPtMove_psi_fst__593f73f6caa4
