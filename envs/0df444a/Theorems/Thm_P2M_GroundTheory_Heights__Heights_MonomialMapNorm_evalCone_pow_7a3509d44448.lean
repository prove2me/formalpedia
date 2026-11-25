-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_evalCone_pow_7a3509d44448
-- name    : P2M_GroundTheory_Heights__Heights_MonomialMapNorm_evalCone_pow_7a3509d44448
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:50:43.457032+00:00
-- url     : https://prove2.me/theorems/02d0b9c5-108f-4f1c-9b47-81d06e7af88a
-- title:
--   P2 M Ground Theory Heights  Heights Monomial Map Norm eval Cone pow 7a3509d44448: P2 M Ground Theory Heights  Heights Monomial Map Norm eval Cone pow 7a3509d44448
-- statement:
--   The P2 M Ground Theory Heights  Heights Monomial Map Norm eval Cone pow 7a3509d44448 construction uses the P2 M Ground Theory Heights  Heights Monomial Map Norm eval Cone pow 7a3509d44448 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L21-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroBis
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
open GroundTheory.Heights₂.Heights.MonomialMapNorm
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_MonomialMapNorm_evalCone_pow_7a3509d44448 (z : Cone n ℂ) (f : MvPolynomial (Coord n) ℤ) (m : ℕ) :
    evalCone z (f ^ m) = evalCone z f ^ m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MonomialMapNorm».«evalCone_pow» := P2M_GroundTheory_Heights__Heights_MonomialMapNorm_evalCone_pow_7a3509d44448
