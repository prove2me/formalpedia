-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistMul_twistMul_e492a93d5146
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twistMul_twistMul_e492a93d5146
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:15:28.448062+00:00
-- url     : https://prove2.me/theorems/47e064bc-022a-53aa-9b21-aa13e8427e08
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman twist Mul twist Mul e492a93d5146: P2 M Ground Theory Heights  Heights Kleiman twist Mul twist Mul e492a93d5146
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman twist Mul twist Mul e492a93d5146 construction uses the P2 M Ground Theory Heights  Heights Kleiman twist Mul twist Mul e492a93d5146 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistAlg.lean#L82-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistAlg.lean#L82-L86

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twistMul_twistMul_e492a93d5146 (M : SubSystem S x Ω) (q n : ℕ) (m a : ℤ) :
    twistMul (twistMul M q m) n a = twistMul M (n * q) (n * m + a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twistMul_twistMul» := P2M_GroundTheory_Heights__Heights_Kleiman_twistMul_twistMul_e492a93d5146
