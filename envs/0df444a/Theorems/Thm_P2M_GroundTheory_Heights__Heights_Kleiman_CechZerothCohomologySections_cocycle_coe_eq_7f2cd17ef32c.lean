-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechZerothCohomologySections_cocycle_coe_eq_7f2cd17ef32c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CechZerothCohomologySections_cocycle_coe_eq_7f2cd17ef32c
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:53:35.301847+00:00
-- url     : https://prove2.me/theorems/52c77b99-0a61-4af7-9449-1f5f606b6d1a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Zeroth Cohomology Sections cocycle coe eq 7f2cd17ef32c: P2 M Ground Theory Heights  Heights Kleiman Cech Zeroth Cohomology Sections cocycle coe eq 7f2c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Zeroth Cohomology Sections cocycle coe eq 7f2cd17ef32c construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Zeroth Cohomology Sections cocycle coe eq 7f2cd17ef32c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExistsMemSupport.lean#L28-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExistsMemSupport.lean#L28-L86

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CechZerothCohomologySections_cocycle_coe_eq_7f2cd17ef32c (F : SubSystem S x E) {s : Cech.Cochain (fun I => F.sub I) 0}
    (hs : Cech.d (fun I => F.sub I) F.res 0 s = 0) (K K' : Cech.Idx (support x) 0) :
    (s K : E) = (s K' : E) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CechZerothCohomologySections».«cocycle_coe_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_CechZerothCohomologySections_cocycle_coe_eq_7f2cd17ef32c
