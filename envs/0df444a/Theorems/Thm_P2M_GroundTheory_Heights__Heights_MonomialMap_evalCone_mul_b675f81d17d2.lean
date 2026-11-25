-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMap_evalCone_mul_b675f81d17d2
-- name    : P2M_GroundTheory_Heights__Heights_MonomialMap_evalCone_mul_b675f81d17d2
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:51:23.619075+00:00
-- url     : https://prove2.me/theorems/7541d8fb-5c8c-5c9b-a9df-3f7b0ecc3300
-- title:
--   P2 M Ground Theory Heights  Heights Monomial Map eval Cone mul b675f81d17d2: P2 M Ground Theory Heights  Heights Monomial Map eval Cone mul b675f81d17d2
-- statement:
--   The P2 M Ground Theory Heights  Heights Monomial Map eval Cone mul b675f81d17d2 construction uses the P2 M Ground Theory Heights  Heights Monomial Map eval Cone mul b675f81d17d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroAlt.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroAlt.lean#L16-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroAlt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_mul_5bfd3b05f445

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

theorem P2M_GroundTheory_Heights__Heights_MonomialMap_evalCone_mul_b675f81d17d2 (z : Cone n ℂ) (f g : MvPolynomial (Coord n) ℤ) :
    evalCone z (f * g) = evalCone z f * evalCone z g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MonomialMap».«evalCone_mul» := P2M_GroundTheory_Heights__Heights_MonomialMap_evalCone_mul_b675f81d17d2
