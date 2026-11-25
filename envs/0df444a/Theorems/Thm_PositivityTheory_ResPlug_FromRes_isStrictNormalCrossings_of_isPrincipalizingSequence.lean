-- Prove2me | Theorems.Thm_PositivityTheory_ResPlug_FromRes_isStrictNormalCrossings_of_isPrincipalizingSequence
-- name    : PositivityTheory.ResPlug.FromRes.isStrictNormalCrossings_of_isPrincipalizingSequence
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:51:10.198309+00:00
-- url     : https://prove2.me/theorems/0e8b4e78-947f-5e95-a705-7104e7086753
-- title:
--   From Res: is Strict Normal Crossings of is Principalizing Sequence
-- statement:
--   The From Res construction uses the is Strict Normal Crossings of is Principalizing Sequence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ResolutionCharZero/FromResSnc.lean#L428-L442
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ResolutionCharZero/FromResSnc.lean#L428-L442

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

theorem PositivityTheory.ResPlug.FromRes.isStrictNormalCrossings_of_isPrincipalizingSequence {k : Type} [Field k] [CharZero k] {X : Scheme.{0}}
    {p : X ⟶ Spec (CommRingCat.of k)} [Smooth p] [LocallyOfFiniteType p] [QuasiCompact p]
    {I : X.IdealSheafData} {E : List X.IdealSheafData} {s : BlowupSequence X}
    (hE : HasSimpleNormalCrossings p E) (h : IsPrincipalizingSequence p I E s) :
    IsStrictNormalCrossings (reducedPreimage s.topMap I.support) := by sorry
