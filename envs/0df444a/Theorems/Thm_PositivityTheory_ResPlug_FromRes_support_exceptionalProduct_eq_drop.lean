-- Prove2me | Theorems.Thm_PositivityTheory_ResPlug_FromRes_support_exceptionalProduct_eq_drop
-- name    : PositivityTheory.ResPlug.FromRes.support_exceptionalProduct_eq_drop
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:52:45.835318+00:00
-- url     : https://prove2.me/theorems/2f18785f-e649-57a2-8f62-416ff0f32e90
-- title:
--   From Res: support exceptional Product eq drop
-- statement:
--   The From Res construction uses the support exceptional Product eq drop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ResolutionCharZero/FromResSnc.lean#L363-L426
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ResolutionCharZero/FromResSnc.lean#L363-L426

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Statements
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsClopen
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsChartNormalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsOpenImmersion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
import Definitions.Def_Development_WeilBound_CoreStatements_ResolutionCharZero_FromResSnc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open PositivityTheory PositivityTheory.ResPlug PositivityTheory.ResPlug.FromRes
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem PositivityTheory.ResPlug.FromRes.support_exceptionalProduct_eq_drop {k : Type} [Field k] {X : Scheme.{0}}
    {p : X ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType p] {I : X.IdealSheafData} {E : List X.IdealSheafData}
    {s : BlowupSequence X} (h : IsPrincipalizingSequence p I E s) :
    ∃ boundary : ∀ i : ℕ, List (s.obj i).IdealSheafData,
      (∀ i, i ≤ s.length → HasSimpleNormalCrossings (s.structMap i ≫ p) (boundary i)) ∧
      ((s.exceptionalProduct s.length).support : Set s.top) =
        (((boundary s.length).drop E.length).prod.support : Set s.top) := by sorry
