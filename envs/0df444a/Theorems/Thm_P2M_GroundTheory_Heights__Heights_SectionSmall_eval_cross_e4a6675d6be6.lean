-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionSmall_eval_cross_e4a6675d6be6
-- name    : P2M_GroundTheory_Heights__Heights_SectionSmall_eval_cross_e4a6675d6be6
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:37:31.454395+00:00
-- url     : https://prove2.me/theorems/8f8c20a3-4c8d-4a32-8177-18030712e7db
-- title:
--   P2 M Ground Theory Heights  Heights Section Small eval cross e4a6675d6be6: P2 M Ground Theory Heights  Heights Section Small eval cross e4a6675d6be6
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Small eval cross e4a6675d6be6 construction uses the P2 M Ground Theory Heights  Heights Section Small eval cross e4a6675d6be6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PSectionSmall.lean#L57-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PSectionSmall.lean#L57-L69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PSectionSmall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.SectionSmall

theorem P2M_GroundTheory_Heights__Heights_SectionSmall_eval_cross_e4a6675d6be6 {P : ArithVariety n} {a : ι → ℤ} (s : IntegralSection P a)
    {p q e m : MvPolynomial (Coord n) ℤ} (hpq : s.den * p - s.num * q ∈ P.ideal)
    (hem : s.den * e - s.num * m ∈ P.ideal) {z : Cone n ℂ} (hz : z ∈ P.points ℂ) :
    evalCone z e * evalCone z q = evalCone z p * evalCone z m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionSmall».«eval_cross» := P2M_GroundTheory_Heights__Heights_SectionSmall_eval_cross_e4a6675d6be6
