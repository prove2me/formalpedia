-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_comap_ker_subscheme__comp_6d441ab4fd0b
-- name    : P2M_FunctorialResolution_EmbeddedResolution_comap_ker_subscheme__comp_6d441ab4fd0b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:42:41.011001+00:00
-- url     : https://prove2.me/theorems/613ecf4f-6982-4ed5-a7a3-45a372f678b4
-- title:
--   P2 M Functorial Resolution Embedded Resolution comap ker subscheme  comp 6d441ab4fd0b: P2 M Functorial Resolution Embedded Resolution comap ker subscheme  comp 6d441ab4fd0b
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution comap ker subscheme  comp 6d441ab4fd0b construction uses the P2 M Functorial Resolution Embedded Resolution comap ker subscheme  comp 6d441ab4fd0b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/StrictTransform.lean#L181-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/StrictTransform.lean#L181-L184

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
import Theorems.Thm_P2M_FunctorialResolution_Blowup_comap_ker_subscheme__comp_0b937eab6fcc

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

theorem P2M_FunctorialResolution_EmbeddedResolution_comap_ker_subscheme__comp_6d441ab4fd0b {A B : Scheme.{u}} (K : A.IdealSheafData) (f : A ⟶ B)
    [IsOpenImmersion f] [QuasiCompact K.subschemeι] [QuasiCompact (K.subschemeι ≫ f)] :
    (K.subschemeι ≫ f).ker.comap f = K := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«comap_ker_subschemeι_comp» := P2M_FunctorialResolution_EmbeddedResolution_comap_ker_subscheme__comp_6d441ab4fd0b
