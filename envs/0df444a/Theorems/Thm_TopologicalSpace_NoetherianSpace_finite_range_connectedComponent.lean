-- Prove2me | Theorems.Thm_TopologicalSpace_NoetherianSpace_finite_range_connectedComponent
-- name    : TopologicalSpace.NoetherianSpace.finite_range_connectedComponent
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:10:40.936004+00:00
-- url     : https://prove2.me/theorems/8f2a6ca4-5a9c-42d0-a33d-591b1e299820
-- title:
--   Noetherian Space: finite range connected Component
-- statement:
--   The Noetherian Space construction uses the finite range connected Component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/SchemeMorphismProperties.lean#L119-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/SchemeMorphismProperties.lean#L119-L136

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

theorem TopologicalSpace.NoetherianSpace.finite_range_connectedComponent (Y : Type*) [TopologicalSpace Y] [NoetherianSpace Y] :
    (Set.range fun x : Y => connectedComponent x).Finite := by sorry
