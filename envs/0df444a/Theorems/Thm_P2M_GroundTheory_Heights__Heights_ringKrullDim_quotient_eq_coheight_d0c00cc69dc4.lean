-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_eq_coheight_d0c00cc69dc4
-- name    : P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_eq_coheight_d0c00cc69dc4
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:11.155936+00:00
-- url     : https://prove2.me/theorems/e42fc98d-afc4-455f-bc38-c5b99fbdb82c
-- title:
--   P2 M Ground Theory Heights  Heights ring Krull Dim quotient eq coheight d0c00cc69dc4: P2 M Ground Theory Heights  Heights ring Krull Dim quotient eq coheight d0c00cc69dc4
-- statement:
--   The P2 M Ground Theory Heights  Heights ring Krull Dim quotient eq coheight d0c00cc69dc4 construction uses the P2 M Ground Theory Heights  Heights ring Krull Dim quotient eq coheight d0c00cc69dc4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/HeightCoheightQuotient.lean#L6-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/HeightCoheightQuotient.lean#L6-L13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_HeightCoheightQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights

theorem P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_eq_coheight_d0c00cc69dc4 {B : Type*} [CommRing B] (P : Ideal B) [hP : P.IsPrime] :
    ringKrullDim (B ⧸ P) = Order.coheight (⟨P, hP⟩ : PrimeSpectrum B) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ringKrullDim_quotient_eq_coheight» := P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_eq_coheight_d0c00cc69dc4
