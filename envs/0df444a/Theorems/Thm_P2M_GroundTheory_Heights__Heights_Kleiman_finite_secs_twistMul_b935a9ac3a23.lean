-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_finite_secs_twistMul_b935a9ac3a23
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_finite_secs_twistMul_b935a9ac3a23
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:00:14.989888+00:00
-- url     : https://prove2.me/theorems/9aef1648-927a-4231-8b01-86e304e4c657
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman finite secs twist Mul b935a9ac3a23: P2 M Ground Theory Heights  Heights Kleiman finite secs twist Mul b935a9ac3a23
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman finite secs twist Mul b935a9ac3a23 construction uses the P2 M Ground Theory Heights  Heights Kleiman finite secs twist Mul b935a9ac3a23 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountTop.lean#L68-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountTop.lean#L68-L91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountTopSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDimSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDegreeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountTop
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
open MvPolynomial Filter
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_finite_secs_twistMul_b935a9ac3a23 (hTF : TwistFinite.Statement.{u, w}) (Nb : LineBundle k x) {r : ℕ}
    {h : Fin (r + 1) → Ω} (hx : x ≠ 0) (hV : IsVeryAmpleBy Nb.toSubSystem h) (n : ℕ) :
    Module.Finite k (twistMul Nb.toSubSystem n 0).secs := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«finite_secs_twistMul» := P2M_GroundTheory_Heights__Heights_Kleiman_finite_secs_twistMul_b935a9ac3a23
