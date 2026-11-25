-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_chartRing_extend_09d18153b28b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_mem_chartRing_extend_09d18153b28b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:23:24.725895+00:00
-- url     : https://prove2.me/theorems/5cd282c1-a366-430f-bd23-1e4ca81b2dce
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman mem chart Ring extend 09d18153b28b: P2 M Ground Theory Heights  Heights Kleiman mem chart Ring extend 09d18153b28b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman mem chart Ring extend 09d18153b28b construction uses the P2 M Ground Theory Heights  Heights Kleiman mem chart Ring extend 09d18153b28b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExtendTwist.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExtendTwist.lean#L30-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist
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
open MvPolynomial
open scoped Pointwise
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {F : Type u} [Field F] [Algebra S F] [Algebra F Ω] [IsScalarTower S F Ω]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_mem_chartRing_extend_09d18153b28b {I : Chart x} {a : Ω} (ha : a ∈ chartRing S x I) :
    a ∈ chartRing F x I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«mem_chartRing_extend» := P2M_GroundTheory_Heights__Heights_Kleiman_mem_chartRing_extend_09d18153b28b
