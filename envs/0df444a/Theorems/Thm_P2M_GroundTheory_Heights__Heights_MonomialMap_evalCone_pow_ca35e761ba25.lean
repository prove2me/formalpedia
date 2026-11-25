-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMap_evalCone_pow_ca35e761ba25
-- name    : P2M_GroundTheory_Heights__Heights_MonomialMap_evalCone_pow_ca35e761ba25
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:49:53.066265+00:00
-- url     : https://prove2.me/theorems/899ea14b-adc3-434e-acb5-251c9e210b91
-- title:
--   P2 M Ground Theory Heights  Heights Monomial Map eval Cone pow ca35e761ba25: P2 M Ground Theory Heights  Heights Monomial Map eval Cone pow ca35e761ba25
-- statement:
--   The P2 M Ground Theory Heights  Heights Monomial Map eval Cone pow ca35e761ba25 construction uses the P2 M Ground Theory Heights  Heights Monomial Map eval Cone pow ca35e761ba25 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroAlt.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroAlt.lean#L21-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroAlt
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
open GroundTheory.Heights₂.Heights.MonomialMap
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_MonomialMap_evalCone_pow_ca35e761ba25 (z : Cone n ℂ) (f : MvPolynomial (Coord n) ℤ) (m : ℕ) :
    evalCone z (f ^ m) = evalCone z f ^ m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MonomialMap».«evalCone_pow» := P2M_GroundTheory_Heights__Heights_MonomialMap_evalCone_pow_ca35e761ba25
