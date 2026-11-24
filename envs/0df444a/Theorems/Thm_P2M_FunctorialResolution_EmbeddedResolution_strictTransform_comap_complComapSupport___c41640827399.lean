-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_strictTransform_comap_complComapSupport___c41640827399
-- name    : P2M_FunctorialResolution_EmbeddedResolution_strictTransform_comap_complComapSupport___c41640827399
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:42:49.185128+00:00
-- url     : https://prove2.me/theorems/100747fb-d799-4537-a727-b860147d0a1b
-- title:
--   P2 M Functorial Resolution Embedded Resolution strict Transform comap compl Comap Support   c41640827399: P2 M Functorial Resolution Embedded Resolution strict Transform comap compl Comap Support   c4
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution strict Transform comap compl Comap Support   c41640827399 construction uses the P2 M Functorial Resolution Embedded Resolution strict Transform comap compl Comap Support   c41640827399 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/StrictTransformOffCenter.lean#L21-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/StrictTransformOffCenter.lean#L21-L38

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransformOffCenter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem P2M_FunctorialResolution_EmbeddedResolution_strictTransform_comap_complComapSupport___c41640827399 {X X₁ : Scheme.{u}} [IsNoetherian X₁]
    (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    (Blowup.strictTransform π Z D).comap (Scheme.Opens.ι (complComapSupport π Z)) =
      (D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z)) := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«strictTransform_comap_complComapSupport_ι» := P2M_FunctorialResolution_EmbeddedResolution_strictTransform_comap_complComapSupport___c41640827399
