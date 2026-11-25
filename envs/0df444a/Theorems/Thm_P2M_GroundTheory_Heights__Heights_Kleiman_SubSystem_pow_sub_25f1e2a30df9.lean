-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_pow_sub_25f1e2a30df9
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_pow_sub_25f1e2a30df9
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:07:02.618161+00:00
-- url     : https://prove2.me/theorems/a5c32c7e-a2e4-4804-a419-3187b1f1c785
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sub System pow sub 25f1e2a30df9: P2 M Ground Theory Heights  Heights Kleiman Sub System pow sub 25f1e2a30df9
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sub System pow sub 25f1e2a30df9 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sub System pow sub 25f1e2a30df9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistAlg.lean#L36-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistAlg.lean#L36-L44

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
open GroundTheory.Heights₂.Heights.Kleiman.SubSystem

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_pow_sub_25f1e2a30df9 (Q : SubSystem S x Ω) (n : ℕ) (I : Chart x) : (Q.pow n).sub I = Q.sub I ^ n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SubSystem».«pow_sub» := P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_pow_sub_25f1e2a30df9
