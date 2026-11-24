-- Prove2me | Theorems.Thm_PositivityTheory_ResPlug_FromRes_inSNCPosition_of_hasSNC
-- name    : PositivityTheory.ResPlug.FromRes.inSNCPosition_of_hasSNC
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:05:43.547797+00:00
-- url     : https://prove2.me/theorems/00aa52b3-12fa-4374-9709-455899e0abd1
-- title:
--   From Res: in SNCPosition of has SNC
-- statement:
--   The From Res construction uses the in SNCPosition of has SNC property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ResolutionCharZero/FromResSnc.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ResolutionCharZero/FromResSnc.lean#L16-L20

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

theorem PositivityTheory.ResPlug.FromRes.inSNCPosition_of_hasSNC {X : Scheme.{0}} {k : Type} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
    {E : List X.IdealSheafData} (h : HasSimpleNormalCrossings p E) : InStrictNormalCrossingPosition p E := by sorry
