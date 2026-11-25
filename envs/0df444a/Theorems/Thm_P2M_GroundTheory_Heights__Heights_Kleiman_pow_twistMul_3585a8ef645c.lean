-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_pow_twistMul_3585a8ef645c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_pow_twistMul_3585a8ef645c
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:15:16.277031+00:00
-- url     : https://prove2.me/theorems/f743763a-f1bb-5cdb-9c33-e783f65eb332
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman pow twist Mul 3585a8ef645c: P2 M Ground Theory Heights  Heights Kleiman pow twist Mul 3585a8ef645c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman pow twist Mul 3585a8ef645c construction uses the P2 M Ground Theory Heights  Heights Kleiman pow twist Mul 3585a8ef645c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistAlg.lean#L88-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistAlg.lean#L88-L93

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_pow_twistMul_3585a8ef645c (M : SubSystem S x Ω) (q j : ℕ) (m : ℤ) :
    (twistMul M q m).pow j = twistMul M (j * q) (j * m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«pow_twistMul» := P2M_GroundTheory_Heights__Heights_Kleiman_pow_twistMul_3585a8ef645c
