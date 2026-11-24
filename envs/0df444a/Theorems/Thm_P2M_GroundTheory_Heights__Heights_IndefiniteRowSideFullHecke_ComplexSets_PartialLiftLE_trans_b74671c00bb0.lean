-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PartialLiftLE_trans_b74671c00bb0
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PartialLiftLE_trans_b74671c00bb0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:53.290611+00:00
-- url     : https://prove2.me/theorems/5ea5ede3-12a8-4373-a32c-b9855cb446a4
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Partial Lift LE trans b74671c00bb0: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Part
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Partial Lift LE trans b74671c00bb0 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Partial Lift LE trans b74671c00bb0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPerfectFieldExtensionFormallySmoothPartialLifts.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPerfectFieldExtensionFormallySmoothPartialLifts.lean#L18-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPerfectFieldExtensionFormallySmoothFrobeniusLift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPerfectFieldExtensionFormallySmoothPartialLifts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Polynomial IntermediateField
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
variable {F K B : Type*} [Field F] [Field K] [Algebra F K] [CommRing B] [Algebra F B]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PartialLiftLE_trans_b74671c00bb0 {a b d : Σ L : IntermediateField F K, L →ₐ[F] B} (h₁ : PartialLiftLE a b)
    (h₂ : PartialLiftLE b d) : PartialLiftLE a d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«PartialLiftLE».«trans» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PartialLiftLE_trans_b74671c00bb0
