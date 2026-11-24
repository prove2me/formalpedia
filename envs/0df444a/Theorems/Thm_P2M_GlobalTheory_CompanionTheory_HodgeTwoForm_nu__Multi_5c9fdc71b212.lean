-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_HodgeTwoForm_nu__Multi_5c9fdc71b212
-- name    : P2M_GlobalTheory_CompanionTheory_HodgeTwoForm_nu__Multi_5c9fdc71b212
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:23:42.14381+00:00
-- url     : https://prove2.me/theorems/2d674336-ff47-447f-94ab-3b68dff95aaa
-- title:
--   P2 M Global Theory Companion Theory Hodge Two Form nu  Multi 5c9fdc71b212: P2 M Global Theory Companion Theory Hodge Two Form nu  Multi 5c9fdc71b212
-- statement:
--   The P2 M Global Theory Companion Theory Hodge Two Form nu  Multi 5c9fdc71b212 construction uses the P2 M Global Theory Companion Theory Hodge Two Form nu  Multi 5c9fdc71b212 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeFunctionalTwoFormNaturality.lean#L112-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeFunctionalTwoFormNaturality.lean#L112-L119

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeFunctionalTwoFormNaturality
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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeTwoForm
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem P2M_GlobalTheory_CompanionTheory_HodgeTwoForm_nu__Multi_5c9fdc71b212 (a b : Glob1 F) (T : C) :
    nu F (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T) := by sorry

alias «GlobalTheory».«CompanionTheory».«HodgeTwoForm».«nu_ιMulti» := P2M_GlobalTheory_CompanionTheory_HodgeTwoForm_nu__Multi_5c9fdc71b212
