-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_HodgeLow_mk__comp_dd1199b7125f
-- name    : P2M_GlobalTheory_CompanionTheory_HodgeLow_mk__comp_dd1199b7125f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:03:17.674573+00:00
-- url     : https://prove2.me/theorems/55408235-37e2-442f-925e-de39c7f45dfb
-- title:
--   P2 M Global Theory Companion Theory Hodge Low mk  comp dd1199b7125f: P2 M Global Theory Companion Theory Hodge Low mk  comp dd1199b7125f
-- statement:
--   The P2 M Global Theory Companion Theory Hodge Low mk  comp dd1199b7125f construction uses the P2 M Global Theory Companion Theory Hodge Low mk  comp dd1199b7125f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PullbackZeroCochainsAlgebraMap.lean#L84-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PullbackZeroCochainsAlgebraMap.lean#L84-L88

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

theorem P2M_GlobalTheory_CompanionTheory_HodgeLow_mk__comp_dd1199b7125f (G : C' ⥤ C) {T T' : C'} (φ : T ⟶ T') :
    ComposableArrows.mk₁ φ ⋙ G = ComposableArrows.mk₁ (G.map φ) := by sorry

alias «GlobalTheory».«CompanionTheory».«HodgeLow».«mk₁_comp» := P2M_GlobalTheory_CompanionTheory_HodgeLow_mk__comp_dd1199b7125f
