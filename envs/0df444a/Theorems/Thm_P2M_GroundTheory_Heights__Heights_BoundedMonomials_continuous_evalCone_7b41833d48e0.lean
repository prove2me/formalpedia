-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BoundedMonomials_continuous_evalCone_7b41833d48e0
-- name    : P2M_GroundTheory_Heights__Heights_BoundedMonomials_continuous_evalCone_7b41833d48e0
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:18:28.930303+00:00
-- url     : https://prove2.me/theorems/8e1f292f-cbf7-42d2-b145-b291f997834f
-- title:
--   P2 M Ground Theory Heights  Heights Bounded Monomials continuous eval Cone 7b41833d48e0: P2 M Ground Theory Heights  Heights Bounded Monomials continuous eval Cone 7b41833d48e0
-- statement:
--   The P2 M Ground Theory Heights  Heights Bounded Monomials continuous eval Cone 7b41833d48e0 construction uses the P2 M Ground Theory Heights  Heights Bounded Monomials continuous eval Cone 7b41833d48e0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZero.lean#L45-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZero.lean#L45-L54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZero
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
open GroundTheory.Heights₂.Heights.BoundedMonomials
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_BoundedMonomials_continuous_evalCone_7b41833d48e0 (f : MvPolynomial (Coord n) ℤ) :
    Continuous fun z : Cone n ℂ ↦ evalCone z f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BoundedMonomials».«continuous_evalCone» := P2M_GroundTheory_Heights__Heights_BoundedMonomials_continuous_evalCone_7b41833d48e0
