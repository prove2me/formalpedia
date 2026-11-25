-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_sub_twistMul_2727aa0a3e72
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KThm_sub_twistMul_2727aa0a3e72
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:40:01.596095+00:00
-- url     : https://prove2.me/theorems/f2f46a99-e170-4c21-a2e7-00fde4235e51
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KThm sub twist Mul 2727aa0a3e72: P2 M Ground Theory Heights  Heights Kleiman KThm sub twist Mul 2727aa0a3e72
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KThm sub twist Mul 2727aa0a3e72 construction uses the P2 M Ground Theory Heights  Heights Kleiman KThm sub twist Mul 2727aa0a3e72 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleNefPlusAmple.lean#L57-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleNefPlusAmple.lean#L57-L62

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KThm_sub_twistMul_2727aa0a3e72 (M : SubSystem S x Ω) (p : ℕ) (m : ℤ) (I : Chart x) {i : Fin (N + 1)}
    (hi : i ∈ I.1) :
    (twistMul M p m).sub I = M.sub I ^ p * Submodule.span (chartRing S x I) {x i ^ m} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KThm».«sub_twistMul» := P2M_GroundTheory_Heights__Heights_Kleiman_KThm_sub_twistMul_2727aa0a3e72
