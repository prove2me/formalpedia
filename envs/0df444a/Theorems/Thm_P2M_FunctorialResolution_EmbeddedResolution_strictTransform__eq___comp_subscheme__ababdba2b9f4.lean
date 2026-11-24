-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_strictTransform__eq___comp_subscheme__ababdba2b9f4
-- name    : P2M_FunctorialResolution_EmbeddedResolution_strictTransform__eq___comp_subscheme__ababdba2b9f4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:58.723799+00:00
-- url     : https://prove2.me/theorems/c48fa52c-8515-4cd1-a0c0-49ea5a7d2ac3
-- title:
--   P2 M Functorial Resolution Embedded Resolution strict Transform  eq   comp subscheme  ababdba2b9f4: P2 M Functorial Resolution Embedded Resolution strict Transform  eq   comp subscheme  ababdba2b9f4
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution strict Transform  eq   comp subscheme  ababdba2b9f4 construction uses the P2 M Functorial Resolution Embedded Resolution strict Transform  eq   comp subscheme  ababdba2b9f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/StrictTransform.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/StrictTransform.lean#L35-L37

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupIsoOffCenter
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_OpenImmersionAppLE
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ReducedSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
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

theorem P2M_FunctorialResolution_EmbeddedResolution_strictTransform__eq___comp_subscheme__ababdba2b9f4 {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    strictTransformι π Z D =
      Scheme.Opens.ι (strictTransformOpens π Z D) ≫ (D.comap π).subschemeι := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«strictTransformι_eq_ι_comp_subschemeι» := P2M_FunctorialResolution_EmbeddedResolution_strictTransform__eq___comp_subscheme__ababdba2b9f4
