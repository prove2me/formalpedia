-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_pow_sub_one_mem_span_ca487896d56f
-- name    : P2M_GroundTheory_Heights__Heights_pow_sub_one_mem_span_ca487896d56f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:21.101092+00:00
-- url     : https://prove2.me/theorems/e72080c1-0db5-4af1-9990-649103f5d654
-- title:
--   P2 M Ground Theory Heights  Heights pow sub one mem span ca487896d56f: P2 M Ground Theory Heights  Heights pow sub one mem span ca487896d56f
-- statement:
--   The P2 M Ground Theory Heights  Heights pow sub one mem span ca487896d56f construction uses the P2 M Ground Theory Heights  Heights pow sub one mem span ca487896d56f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RadicalAwayRabinowitsch.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RadicalAwayRabinowitsch.lean#L28-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RadicalAwayRabinowitsch
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
open MvPolynomial
noncomputable section
variable {R : Type*} [CommRing R] {ι : Type*}

theorem P2M_GroundTheory_Heights__Heights_pow_sub_one_mem_span_ca487896d56f (g : MvPolynomial ι R) (k : ℕ) :
    (X none * rename some g) ^ k - 1 ∈
      (Ideal.span {X none * rename some g - 1} : Ideal (MvPolynomial (Option ι) R)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«pow_sub_one_mem_span» := P2M_GroundTheory_Heights__Heights_pow_sub_one_mem_span_ca487896d56f
