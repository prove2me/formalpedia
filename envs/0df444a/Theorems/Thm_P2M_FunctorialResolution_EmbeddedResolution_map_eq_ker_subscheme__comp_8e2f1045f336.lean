-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_map_eq_ker_subscheme__comp_8e2f1045f336
-- name    : P2M_FunctorialResolution_EmbeddedResolution_map_eq_ker_subscheme__comp_8e2f1045f336
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:59.605811+00:00
-- url     : https://prove2.me/theorems/0e0b721a-8023-44f4-b044-1663bc5e57f5
-- title:
--   P2 M Functorial Resolution Embedded Resolution map eq ker subscheme  comp 8e2f1045f336: P2 M Functorial Resolution Embedded Resolution map eq ker subscheme  comp 8e2f1045f336
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution map eq ker subscheme  comp 8e2f1045f336 construction uses the P2 M Functorial Resolution Embedded Resolution map eq ker subscheme  comp 8e2f1045f336 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/ClosedEmbedding/StrictTransformClosedImmersion.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/ClosedEmbedding/StrictTransformClosedImmersion.lean#L39-L41

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

theorem P2M_FunctorialResolution_EmbeddedResolution_map_eq_ker_subscheme__comp_8e2f1045f336 {U V : Scheme.{u}} (j : U ⟶ V) (K : U.IdealSheafData) :
    K.map j = Scheme.Hom.ker (K.subschemeι ≫ j) := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«map_eq_ker_subschemeι_comp» := P2M_FunctorialResolution_EmbeddedResolution_map_eq_ker_subscheme__comp_8e2f1045f336
