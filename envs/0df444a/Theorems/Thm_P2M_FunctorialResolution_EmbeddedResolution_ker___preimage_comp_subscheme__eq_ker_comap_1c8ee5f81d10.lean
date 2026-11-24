-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_ker___preimage_comp_subscheme__eq_ker_comap_1c8ee5f81d10
-- name    : P2M_FunctorialResolution_EmbeddedResolution_ker___preimage_comp_subscheme__eq_ker_comap_1c8ee5f81d10
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:18.414827+00:00
-- url     : https://prove2.me/theorems/6923da05-3c4a-415f-a024-948c33a54a16
-- title:
--   P2 M Functorial Resolution Embedded Resolution ker   preimage comp subscheme  eq ker comap 1c8ee5f81d10: P2 M Functorial Resolution Embedded Resolution ker   preimage comp subscheme  eq ker comap 1c8e
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution ker   preimage comp subscheme  eq ker comap 1c8ee5f81d10 construction uses the P2 M Functorial Resolution Embedded Resolution ker   preimage comp subscheme  eq ker comap 1c8ee5f81d10 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/StrictTransform.lean#L204-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/StrictTransform.lean#L204-L210

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

theorem P2M_FunctorialResolution_EmbeddedResolution_ker___preimage_comp_subscheme__eq_ker_comap_1c8ee5f81d10 {T : Scheme.{u}} (K : T.IdealSheafData) (V : T.Opens) :
    (Scheme.Opens.ι (K.subschemeι ⁻¹ᵁ V) ≫ K.subschemeι).ker =
      ((K.comap (Scheme.Opens.ι V)).subschemeι ≫ Scheme.Opens.ι V).ker := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«ker_ι_preimage_comp_subschemeι_eq_ker_comap» := P2M_FunctorialResolution_EmbeddedResolution_ker___preimage_comp_subscheme__eq_ker_comap_1c8ee5f81d10
