-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_extend_twistSys_b6dc4fb6663d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_extend_twistSys_b6dc4fb6663d
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:21:36.216198+00:00
-- url     : https://prove2.me/theorems/d6197d1e-4f59-4310-86d4-76c6dfe81a79
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sub System extend twist Sys b6dc4fb6663d: P2 M Ground Theory Heights  Heights Kleiman Sub System extend twist Sys b6dc4fb6663d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sub System extend twist Sys b6dc4fb6663d construction uses the P2 M Ground Theory Heights  Heights Kleiman Sub System extend twist Sys b6dc4fb6663d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExtendTwist.lean#L56-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExtendTwist.lean#L56-L60

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_extend_twistSys_b6dc4fb6663d (c : ℤ) : (twistSys S x c).extend F = twistSys F x c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SubSystem».«extend_twistSys» := P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_extend_twistSys_b6dc4fb6663d
