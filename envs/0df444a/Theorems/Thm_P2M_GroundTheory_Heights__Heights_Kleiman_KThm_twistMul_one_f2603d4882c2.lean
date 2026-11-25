-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_twistMul_one_f2603d4882c2
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KThm_twistMul_one_f2603d4882c2
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:57:16.364742+00:00
-- url     : https://prove2.me/theorems/83712a54-d4fe-58b7-a610-46822fda6468
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KThm twist Mul one f2603d4882c2: P2 M Ground Theory Heights  Heights Kleiman KThm twist Mul one f2603d4882c2
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KThm twist Mul one f2603d4882c2 construction uses the P2 M Ground Theory Heights  Heights Kleiman KThm twist Mul one f2603d4882c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleNefPlusAmple.lean#L111-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleNefPlusAmple.lean#L111-L117

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KThm_twistMul_one_f2603d4882c2 (M : SubSystem S x Ω) (c : ℤ) :
    twistMul M 1 c = M.twist (twistSys S x c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KThm».«twistMul_one» := P2M_GroundTheory_Heights__Heights_Kleiman_KThm_twistMul_one_f2603d4882c2
