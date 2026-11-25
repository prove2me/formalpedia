-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistMul_sub_ecdec4e29c5d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twistMul_sub_ecdec4e29c5d
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:07:36.406305+00:00
-- url     : https://prove2.me/theorems/5a2075e5-ae1d-513f-bcf5-167a4f68b4df
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman twist Mul sub ecdec4e29c5d: P2 M Ground Theory Heights  Heights Kleiman twist Mul sub ecdec4e29c5d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman twist Mul sub ecdec4e29c5d construction uses the P2 M Ground Theory Heights  Heights Kleiman twist Mul sub ecdec4e29c5d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistAlg.lean#L70-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistAlg.lean#L70-L72

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twistMul_sub_ecdec4e29c5d (M : SubSystem S x Ω) (p : ℕ) (m : ℤ) (I : Chart x) :
    (twistMul M p m).sub I = (twistSys S x m).sub I * M.sub I ^ p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twistMul_sub» := P2M_GroundTheory_Heights__Heights_Kleiman_twistMul_sub_ecdec4e29c5d
