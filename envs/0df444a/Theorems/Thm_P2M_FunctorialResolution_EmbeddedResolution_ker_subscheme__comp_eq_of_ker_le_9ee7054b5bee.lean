-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_ker_subscheme__comp_eq_of_ker_le_9ee7054b5bee
-- name    : P2M_FunctorialResolution_EmbeddedResolution_ker_subscheme__comp_eq_of_ker_le_9ee7054b5bee
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:04:14.665085+00:00
-- url     : https://prove2.me/theorems/9c5aae4d-9ad3-422c-806c-07a6e37a32c7
-- title:
--   P2 M Functorial Resolution Embedded Resolution ker subscheme  comp eq of ker le 9ee7054b5bee: P2 M Functorial Resolution Embedded Resolution ker subscheme  comp eq of ker le 9ee7054b5bee
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution ker subscheme  comp eq of ker le 9ee7054b5bee construction uses the P2 M Functorial Resolution Embedded Resolution ker subscheme  comp eq of ker le 9ee7054b5bee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/ClosedEmbedding/StrictTransformClosedImmersion.lean#L43-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/ClosedEmbedding/StrictTransformClosedImmersion.lean#L43-L55

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransformOffCenter
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_StrictTransformClosedImmersion
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

theorem P2M_FunctorialResolution_EmbeddedResolution_ker_subscheme__comp_eq_of_ker_le_9ee7054b5bee {U V : Scheme.{u}} (j : U ⟶ V) [IsClosedImmersion j]
    (L : V.IdealSheafData) (hL : Scheme.Hom.ker j ≤ L) (K : U.IdealSheafData)
    (hK : K = L.comap j) :
    Scheme.Hom.ker (K.subschemeι ≫ j) = L := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«ker_subschemeι_comp_eq_of_ker_le» := P2M_FunctorialResolution_EmbeddedResolution_ker_subscheme__comp_eq_of_ker_le_9ee7054b5bee
