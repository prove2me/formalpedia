-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_CotLoc_spMap_comp__c7aa3ec5f5b7
-- name    : P2M_GlobalTheory_CompanionTheory_CotLoc_spMap_comp__c7aa3ec5f5b7
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:50:56.410693+00:00
-- url     : https://prove2.me/theorems/ffe172c5-8ed1-5ed4-8e59-932c89fcb529
-- title:
--   P2 M Global Theory Companion Theory Cot Loc sp Map comp  c7aa3ec5f5b7: P2 M Global Theory Companion Theory Cot Loc sp Map comp  c7aa3ec5f5b7
-- statement:
--   The P2 M Global Theory Companion Theory Cot Loc sp Map comp  c7aa3ec5f5b7 construction uses the P2 M Global Theory Companion Theory Cot Loc sp Map comp  c7aa3ec5f5b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CotangentLocalOpenChartExists.lean#L8-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CotangentLocalOpenChartExists.lean#L8-L10

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CotangentLocalOpenChartExists
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CotLoc

theorem P2M_GlobalTheory_CompanionTheory_CotLoc_spMap_comp__c7aa3ec5f5b7 {a b c : Type} [CommRing a] [CommRing b] [CommRing c] (f : a →+* b) (g : b →+* c) :
    spMap (g.comp f) = spMap g ≫ spMap f := by sorry

alias «GlobalTheory».«CompanionTheory».«CotLoc».«spMap_comp'» := P2M_GlobalTheory_CompanionTheory_CotLoc_spMap_comp__c7aa3ec5f5b7
