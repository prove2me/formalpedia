-- Prove2me | Theorems.Thm_PositivityTheory_ResPlug_FromRes_isStrictNormalCrossings_of_isPrincipalizingSequence_nil
-- name    : PositivityTheory.ResPlug.FromRes.isStrictNormalCrossings_of_isPrincipalizingSequence_nil
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:56:21.913345+00:00
-- url     : https://prove2.me/theorems/9e09487e-ba46-5d3d-bb3c-dd6417f555f2
-- title:
--   From Res: is Strict Normal Crossings of is Principalizing Sequence nil
-- statement:
--   The From Res construction uses the is Strict Normal Crossings of is Principalizing Sequence nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ResolutionCharZero/FromResSnc.lean#L328-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ResolutionCharZero/FromResSnc.lean#L328-L342

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

theorem PositivityTheory.ResPlug.FromRes.isStrictNormalCrossings_of_isPrincipalizingSequence_nil {k : Type} [Field k] {X : Scheme.{0}}
    {p : X ⟶ Spec (CommRingCat.of k)} [Smooth p] [LocallyOfFiniteType p] [QuasiCompact p]
    {I : X.IdealSheafData} {s : BlowupSequence X}
    (h : IsPrincipalizingSequence p I [] s) :
    IsStrictNormalCrossings (reducedPreimage s.topMap I.support) := by sorry
