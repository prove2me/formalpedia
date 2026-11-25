-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_HodgeLow_mk__comp_6b8f8d3f6a0d
-- name    : P2M_GlobalTheory_CompanionTheory_HodgeLow_mk__comp_6b8f8d3f6a0d
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:04:11.946767+00:00
-- url     : https://prove2.me/theorems/bd671eb5-3565-4f4a-b5f7-45cc6aa849e2
-- title:
--   P2 M Global Theory Companion Theory Hodge Low mk  comp 6b8f8d3f6a0d: P2 M Global Theory Companion Theory Hodge Low mk  comp 6b8f8d3f6a0d
-- statement:
--   The P2 M Global Theory Companion Theory Hodge Low mk  comp 6b8f8d3f6a0d construction uses the P2 M Global Theory Companion Theory Hodge Low mk  comp 6b8f8d3f6a0d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PullbackZeroCochainsAlgebraMap.lean#L80-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PullbackZeroCochainsAlgebraMap.lean#L80-L82

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PullbackZeroCochainsAlgebraMap
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeLow
variable {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
  {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R}

theorem P2M_GlobalTheory_CompanionTheory_HodgeLow_mk__comp_6b8f8d3f6a0d (G : C' ⥤ C) (T : C') :
    ComposableArrows.mk₀ T ⋙ G = ComposableArrows.mk₀ (G.obj T) := by sorry

alias «GlobalTheory».«CompanionTheory».«HodgeLow».«mk₀_comp» := P2M_GlobalTheory_CompanionTheory_HodgeLow_mk__comp_6b8f8d3f6a0d
