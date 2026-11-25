-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Dict_eq_mk__c498ddd0a79f
-- name    : P2M_GlobalTheory_CompanionTheory_Dict_eq_mk__c498ddd0a79f
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:53:40.755847+00:00
-- url     : https://prove2.me/theorems/45f0abc6-59c3-4d41-9ae3-9f089fb2135c
-- title:
--   P2 M Global Theory Companion Theory Dict eq mk  c498ddd0a79f: P2 M Global Theory Companion Theory Dict eq mk  c498ddd0a79f
-- statement:
--   The P2 M Global Theory Companion Theory Dict eq mk  c498ddd0a79f construction uses the P2 M Global Theory Companion Theory Dict eq mk  c498ddd0a79f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechNerveFaceOneZero.lean#L81-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechNerveFaceOneZero.lean#L81-L84

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechNerveFaceOneZero
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
open CategoryTheory.ComposableArrows
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Dict
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem P2M_GlobalTheory_CompanionTheory_Dict_eq_mk__c498ddd0a79f (c : ComposableArrows C 1) (x : c.left ⟶ c.right) (h : c.hom = x) : c = mk₁ x := by sorry

alias «GlobalTheory».«CompanionTheory».«Dict».«eq_mk₁» := P2M_GlobalTheory_CompanionTheory_Dict_eq_mk__c498ddd0a79f
