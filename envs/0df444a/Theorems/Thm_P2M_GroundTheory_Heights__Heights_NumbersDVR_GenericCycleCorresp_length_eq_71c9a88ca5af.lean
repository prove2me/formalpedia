-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericCycleCorresp_length_eq_71c9a88ca5af
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericCycleCorresp_length_eq_71c9a88ca5af
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:40.254859+00:00
-- url     : https://prove2.me/theorems/d0e4fb09-f993-4c4f-8b27-2d8ba2c748ad
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Generic Cycle Corresp length eq 71c9a88ca5af: P2 M Ground Theory Heights  Heights Numbers DVR Generic Cycle Corresp length eq 71c9a88ca5af
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Generic Cycle Corresp length eq 71c9a88ca5af construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Generic Cycle Corresp length eq 71c9a88ca5af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericCycleCorresp.lean#L20-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericCycleCorresp.lean#L20-L132

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericCycleCorresp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericCycleCorresp
variable {S T : Type*} [CommRing S] [CommRing T] [Algebra S T] (M : Submonoid S)
  [IsLocalization M T]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericCycleCorresp_length_eq_71c9a88ca5af (J W : Ideal S) [W.IsPrime] (hW : Disjoint (M : Set S) W)
    [(W.map (algebraMap S T)).IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (S ⧸ J)) =
      Module.length (Localization.AtPrime (W.map (algebraMap S T)))
        (LocalizedModule (W.map (algebraMap S T)).primeCompl (T ⧸ J.map (algebraMap S T))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«GenericCycleCorresp».«length_eq» := P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericCycleCorresp_length_eq_71c9a88ca5af
