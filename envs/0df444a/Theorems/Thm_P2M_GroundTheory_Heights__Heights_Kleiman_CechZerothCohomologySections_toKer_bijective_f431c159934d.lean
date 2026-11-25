-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechZerothCohomologySections_toKer_bijective_f431c159934d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CechZerothCohomologySections_toKer_bijective_f431c159934d
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:53:37.903876+00:00
-- url     : https://prove2.me/theorems/364d236f-b7a5-5900-97c2-54d89ec5e6db
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Zeroth Cohomology Sections to Ker bijective f431c159934d: P2 M Ground Theory Heights  Heights Kleiman Cech Zeroth Cohomology Sections to Ker bijective
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Zeroth Cohomology Sections to Ker bijective f431c159934d construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Zeroth Cohomology Sections to Ker bijective f431c159934d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExistsMemSupport.lean#L107-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExistsMemSupport.lean#L107-L120

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechH0SectionsHypothesesLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsMemSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.CechZerothCohomologySections
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CechZerothCohomologySections_toKer_bijective_f431c159934d (F : SubSystem S x E) (hx : x ≠ 0) : Function.Bijective (toKer F) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CechZerothCohomologySections».«toKer_bijective» := P2M_GroundTheory_Heights__Heights_Kleiman_CechZerothCohomologySections_toKer_bijective_f431c159934d
