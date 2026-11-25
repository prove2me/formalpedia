-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistSys_sub_pow_419ff662fef3
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twistSys_sub_pow_419ff662fef3
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:03:16.161522+00:00
-- url     : https://prove2.me/theorems/406d8d38-04ba-48d7-ad79-ed434755bf9c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman twist Sys sub pow 419ff662fef3: P2 M Ground Theory Heights  Heights Kleiman twist Sys sub pow 419ff662fef3
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman twist Sys sub pow 419ff662fef3 construction uses the P2 M Ground Theory Heights  Heights Kleiman twist Sys sub pow 419ff662fef3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistAlg.lean#L78-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistAlg.lean#L78-L80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
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
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twistSys_sub_pow_419ff662fef3 (c : ℤ) (n : ℕ) (I : Chart x) :
    (twistSys S x c).sub I ^ n = (twistSys S x (n * c)).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twistSys_sub_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_twistSys_sub_pow_419ff662fef3
