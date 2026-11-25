-- Prove2me | Theorems.Thm_PositivityTheory_PrwZar_QiP_powPt_mul
-- name    : PositivityTheory.PrwZar.QiP.powPt_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:54:45.583966+00:00
-- url     : https://prove2.me/theorems/ed965d33-535a-54a0-8fca-1c593e1fc2c5
-- title:
--   Qi P: pow Pt mul
-- statement:
--   The Qi P construction uses the pow Pt mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/ZarhinTrick/QiPtsA.lean#L76-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/ZarhinTrick/QiPtsA.lean#L76-L79

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

theorem PositivityTheory.PrwZar.QiP.powPt_mul (hs : IsFinFlatSub G F h) (φ : F →ₐ[R] S) (a b : ℕ) :
    powPt hs φ (a * b) = powPt hs (powPt hs φ a) b := by sorry
