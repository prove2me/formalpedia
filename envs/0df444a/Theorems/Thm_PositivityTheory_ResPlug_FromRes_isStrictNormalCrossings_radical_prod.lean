-- Prove2me | Theorems.Thm_PositivityTheory_ResPlug_FromRes_isStrictNormalCrossings_radical_prod
-- name    : PositivityTheory.ResPlug.FromRes.isStrictNormalCrossings_radical_prod
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:04:50.504093+00:00
-- url     : https://prove2.me/theorems/b5670ea9-edbc-4d14-b93d-d28db37b55b8
-- title:
--   From Res: is Strict Normal Crossings radical prod
-- statement:
--   The From Res construction uses the is Strict Normal Crossings radical prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ResolutionCharZero/FromResSnc.lean#L162-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ResolutionCharZero/FromResSnc.lean#L162-L237

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

theorem PositivityTheory.ResPlug.FromRes.isStrictNormalCrossings_radical_prod {W : Scheme.{0}} {k : Type} [Field k]
    (p : W ⟶ Spec (CommRingCat.of k)) [Smooth p] (E : List W.IdealSheafData)
    (hE : InStrictNormalCrossingPosition p E) : IsStrictNormalCrossings E.prod.radical := by sorry
