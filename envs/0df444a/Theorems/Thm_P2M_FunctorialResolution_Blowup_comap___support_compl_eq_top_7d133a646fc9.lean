-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_Blowup_comap___support_compl_eq_top_7d133a646fc9
-- name    : P2M_FunctorialResolution_Blowup_comap___support_compl_eq_top_7d133a646fc9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:39.825458+00:00
-- url     : https://prove2.me/theorems/4c38e716-8ea6-4607-abd3-a2a8ed174824
-- title:
--   P2 M Functorial Resolution Blowup comap   support compl eq top 7d133a646fc9: P2 M Functorial Resolution Blowup comap   support compl eq top 7d133a646fc9
-- statement:
--   The P2 M Functorial Resolution Blowup comap   support compl eq top 7d133a646fc9 construction uses the P2 M Functorial Resolution Blowup comap   support compl eq top 7d133a646fc9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupIsoOffCenter.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupIsoOffCenter.lean#L12-L16

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupIsoOffCenter
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
open FunctorialResolution FunctorialResolution.Blowup

theorem P2M_FunctorialResolution_Blowup_comap___support_compl_eq_top_7d133a646fc9 {X : Scheme.{u}} (Z : X.IdealSheafData) :
    Z.comap (Scheme.Opens.ι Z.support.compl) = ⊤ := by sorry

alias «FunctorialResolution».«Blowup».«comap_ι_support_compl_eq_top» := P2M_FunctorialResolution_Blowup_comap___support_compl_eq_top_7d133a646fc9
