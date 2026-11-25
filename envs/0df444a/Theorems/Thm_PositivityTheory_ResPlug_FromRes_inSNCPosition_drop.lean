-- Prove2me | Theorems.Thm_PositivityTheory_ResPlug_FromRes_inSNCPosition_drop
-- name    : PositivityTheory.ResPlug.FromRes.inSNCPosition_drop
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:53:44.750271+00:00
-- url     : https://prove2.me/theorems/64e9bf38-21ee-46fb-bb6a-5aa6ab6e4975
-- title:
--   From Res: in SNCPosition drop
-- statement:
--   The From Res construction uses the in SNCPosition drop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ResolutionCharZero/FromResSnc.lean#L344-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ResolutionCharZero/FromResSnc.lean#L344-L361

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

theorem PositivityTheory.ResPlug.FromRes.inSNCPosition_drop {X : Scheme.{0}} {k : Type} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
    {L : List X.IdealSheafData} (hL : InStrictNormalCrossingPosition p L) (d : ℕ) :
    InStrictNormalCrossingPosition p (L.drop d) := by sorry
