-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ord_pow_irreducible_of_dvr_6fdea97bf37d
-- name    : P2M_GroundTheory_Heights__Heights_ord_pow_irreducible_of_dvr_6fdea97bf37d
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:49:29.841641+00:00
-- url     : https://prove2.me/theorems/2437a572-a2c9-416b-b8fa-a089b86f044e
-- title:
--   P2 M Ground Theory Heights  Heights ord pow irreducible of dvr 6fdea97bf37d: P2 M Ground Theory Heights  Heights ord pow irreducible of dvr 6fdea97bf37d
-- statement:
--   The P2 M Ground Theory Heights  Heights ord pow irreducible of dvr 6fdea97bf37d construction uses the P2 M Ground Theory Heights  Heights ord pow irreducible of dvr 6fdea97bf37d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PointLocalRingOrder.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PointLocalRingOrder.lean#L75-L78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PointLocalRingOrder
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
open MvPolynomial Topology
noncomputable section
variable {σ : Type*}

theorem P2M_GroundTheory_Heights__Heights_ord_pow_irreducible_of_dvr_6fdea97bf37d {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) (e : ℕ) : Ring.ord R (ϖ ^ e) = e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ord_pow_irreducible_of_dvr» := P2M_GroundTheory_Heights__Heights_ord_pow_irreducible_of_dvr_6fdea97bf37d
