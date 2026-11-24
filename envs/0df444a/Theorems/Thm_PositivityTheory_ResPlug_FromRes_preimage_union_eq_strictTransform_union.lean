-- Prove2me | Theorems.Thm_PositivityTheory_ResPlug_FromRes_preimage_union_eq_strictTransform_union
-- name    : PositivityTheory.ResPlug.FromRes.preimage_union_eq_strictTransform_union
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:05:13.237854+00:00
-- url     : https://prove2.me/theorems/e2f9e721-5491-4809-b1d3-ef6ce8f4a95a
-- title:
--   From Res: preimage union eq strict Transform union
-- statement:
--   The From Res construction uses the preimage union eq strict Transform union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ResolutionCharZero/FromResSnc.lean#L255-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ResolutionCharZero/FromResSnc.lean#L255-L276

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

theorem PositivityTheory.ResPlug.FromRes.preimage_union_eq_strictTransform_union {X X₁ : Scheme.{0}} [IsLocallyNoetherian X₁] (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) :
    π.base ⁻¹' (D.support : Set X) ∪ π.base ⁻¹' (Z.support : Set X) =
      ((FunctorialResolution.strictTransform π Z D).support : Set X₁) ∪ π.base ⁻¹' (Z.support : Set X) := by sorry
