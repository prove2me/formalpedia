-- Prove2me | Theorems.Thm_TopologicalSpace_NoetherianSpace_isClosed_setOf_connectedComponent_subset
-- name    : TopologicalSpace.NoetherianSpace.isClosed_setOf_connectedComponent_subset
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:32:20.842917+00:00
-- url     : https://prove2.me/theorems/7f6bc195-34a0-561c-9971-4e379332d439
-- title:
--   Noetherian Space: is Closed set Of connected Component subset
-- statement:
--   The Noetherian Space construction uses the is Closed set Of connected Component subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/SchemeMorphismProperties.lean#L138-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/SchemeMorphismProperties.lean#L138-L167

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open TopologicalSpace TopologicalSpace.NoetherianSpace

theorem TopologicalSpace.NoetherianSpace.isClosed_setOf_connectedComponent_subset (Y : Type*) [TopologicalSpace Y]
    [NoetherianSpace Y] (A : Set Y) : IsClosed {x : Y | connectedComponent x ⊆ A} := by sorry
