-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_twistMul_one_zero_75731c337a9e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KThm_twistMul_one_zero_75731c337a9e
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:59:50.15203+00:00
-- url     : https://prove2.me/theorems/c2bbbbf8-9821-49a0-bfea-e5bbdb31118e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KThm twist Mul one zero 75731c337a9e: P2 M Ground Theory Heights  Heights Kleiman KThm twist Mul one zero 75731c337a9e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KThm twist Mul one zero 75731c337a9e construction uses the P2 M Ground Theory Heights  Heights Kleiman KThm twist Mul one zero 75731c337a9e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleNefPlusAmple.lean#L119-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleNefPlusAmple.lean#L119-L122

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleNefPlusAmple
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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KThm_twistMul_one_zero_75731c337a9e (M : SubSystem S x Ω) : twistMul M 1 0 = M := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KThm».«twistMul_one_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_KThm_twistMul_one_zero_75731c337a9e
