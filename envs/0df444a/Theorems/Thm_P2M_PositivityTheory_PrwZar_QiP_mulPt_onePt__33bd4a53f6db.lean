-- Prove2me | Theorems.Thm_P2M_PositivityTheory_PrwZar_QiP_mulPt_onePt__33bd4a53f6db
-- name    : P2M_PositivityTheory_PrwZar_QiP_mulPt_onePt__33bd4a53f6db
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:44:11.253995+00:00
-- url     : https://prove2.me/theorems/66bf487e-ba96-42c8-ac77-eca6e25e8d88
-- title:
--   P2 M Positivity Theory Prw Zar Qi P mul Pt one Pt  33bd4a53f6db: P2 M Positivity Theory Prw Zar Qi P mul Pt one Pt  33bd4a53f6db
-- statement:
--   The P2 M Positivity Theory Prw Zar Qi P mul Pt one Pt  33bd4a53f6db construction uses the P2 M Positivity Theory Prw Zar Qi P mul Pt one Pt  33bd4a53f6db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/ZarhinTrick/QiPtsA.lean#L85-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/ZarhinTrick/QiPtsA.lean#L85-L87

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_IsFinFlatSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasChartsOfForallIsAffineOpen
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiPtsA
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
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open GlobalTheory.CompanionTheory.Ar.GR
open PositivityTheory PositivityTheory.PrwZar PositivityTheory.PrwZar.QiP
variable {R : Type} [CommRing R] {F : Type} [CommRing F] [Algebra R F]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {h : sp (R₀ := R) F ⟶ G}
variable {S T : Type} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

theorem P2M_PositivityTheory_PrwZar_QiP_mulPt_onePt__33bd4a53f6db (hs : IsFinFlatSub G F h) (φ : F →ₐ[R] S) : mulPt hs φ (onePt hs S) = φ := by sorry

alias «PositivityTheory».«PrwZar».«QiP».«mulPt_onePt'» := P2M_PositivityTheory_PrwZar_QiP_mulPt_onePt__33bd4a53f6db
