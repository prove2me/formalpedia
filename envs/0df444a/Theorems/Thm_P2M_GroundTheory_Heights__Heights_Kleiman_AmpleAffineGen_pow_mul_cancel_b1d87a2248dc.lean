-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_pow_mul_cancel_b1d87a2248dc
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_pow_mul_cancel_b1d87a2248dc
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:12:08.563632+00:00
-- url     : https://prove2.me/theorems/56332781-3010-4f9e-8ae4-7c460ba31f05
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen pow mul cancel b1d87a2248dc: P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen pow mul cancel b1d87a2248dc
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen pow mul cancel b1d87a2248dc construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen pow mul cancel b1d87a2248dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L37-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
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
open GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_pow_mul_cancel_b1d87a2248dc {u p q y : Ω} (hpq : p * q = 1) (e D : ℕ) :
    (u ^ e * p) ^ D * (q ^ D * y) = u ^ (e * D) * y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleAffineGen».«pow_mul_cancel» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_pow_mul_cancel_b1d87a2248dc
