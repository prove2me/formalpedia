-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_extend_twist_7faed6abc2ed
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_extend_twist_7faed6abc2ed
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:23:42.652718+00:00
-- url     : https://prove2.me/theorems/ce46ebde-b35e-56a3-b161-7ef7b347fe9c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sub System extend twist 7faed6abc2ed: P2 M Ground Theory Heights  Heights Kleiman Sub System extend twist 7faed6abc2ed
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sub System extend twist 7faed6abc2ed construction uses the P2 M Ground Theory Heights  Heights Kleiman Sub System extend twist 7faed6abc2ed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExtendTwist.lean#L64-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExtendTwist.lean#L64-L80

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
omit [Algebra S F] [IsScalarTower S F Ω]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_extend_twist_7faed6abc2ed (Q R : SubSystem S x Ω) :
    (Q.twist R).extend F = (Q.extend F).twist (R.extend F) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SubSystem».«extend_twist» := P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_extend_twist_7faed6abc2ed
