-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_lineBundle_twistMul_fe4f7be26a50
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_lineBundle_twistMul_fe4f7be26a50
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:07:10.766514+00:00
-- url     : https://prove2.me/theorems/7d491b36-af53-561f-9ecc-cdcf17e60f43
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists line Bundle twist Mul fe4f7be26a50: P2 M Ground Theory Heights  Heights Kleiman exists line Bundle twist Mul fe4f7be26a50
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists line Bundle twist Mul fe4f7be26a50 construction uses the P2 M Ground Theory Heights  Heights Kleiman exists line Bundle twist Mul fe4f7be26a50 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistAlg.lean#L165-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistAlg.lean#L165-L170

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_lineBundle_twistMul_fe4f7be26a50 (M : LineBundle S x) (p : ℕ) (m : ℤ) :
    ∃ L : LineBundle S x, L.toSubSystem = twistMul M.toSubSystem p m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_lineBundle_twistMul» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_lineBundle_twistMul_fe4f7be26a50
