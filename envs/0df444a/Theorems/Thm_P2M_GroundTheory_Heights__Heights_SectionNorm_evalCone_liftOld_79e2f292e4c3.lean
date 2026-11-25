-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionNorm_evalCone_liftOld_79e2f292e4c3
-- name    : P2M_GroundTheory_Heights__Heights_SectionNorm_evalCone_liftOld_79e2f292e4c3
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:37:14.744795+00:00
-- url     : https://prove2.me/theorems/a3018e46-1df6-4aeb-808e-8274f749dbdc
-- title:
--   P2 M Ground Theory Heights  Heights Section Norm eval Cone lift Old 79e2f292e4c3: P2 M Ground Theory Heights  Heights Section Norm eval Cone lift Old 79e2f292e4c3
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Norm eval Cone lift Old 79e2f292e4c3 construction uses the P2 M Ground Theory Heights  Heights Section Norm eval Cone lift Old 79e2f292e4c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomial.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomial.lean#L21-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomial
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
open GroundTheory.Heights₂.Heights.SectionNorm

theorem P2M_GroundTheory_Heights__Heights_SectionNorm_evalCone_liftOld_79e2f292e4c3 {P : ArithVariety n} (D : AddBlockData P) (w : Cone D.extSizes ℂ)
    (f : MvPolynomial (Coord n) ℤ) : evalCone w (D.liftOld f) = evalCone (D.basePart₂ w) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionNorm».«evalCone_liftOld» := P2M_GroundTheory_Heights__Heights_SectionNorm_evalCone_liftOld_79e2f292e4c3
