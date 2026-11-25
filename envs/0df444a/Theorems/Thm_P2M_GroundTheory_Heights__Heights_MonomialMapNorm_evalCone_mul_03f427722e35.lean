-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_evalCone_mul_03f427722e35
-- name    : P2M_GroundTheory_Heights__Heights_MonomialMapNorm_evalCone_mul_03f427722e35
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:51:45.062393+00:00
-- url     : https://prove2.me/theorems/6b1c097f-a3a7-56e6-b3e4-3c78482f5465
-- title:
--   P2 M Ground Theory Heights  Heights Monomial Map Norm eval Cone mul 03f427722e35: P2 M Ground Theory Heights  Heights Monomial Map Norm eval Cone mul 03f427722e35
-- statement:
--   The P2 M Ground Theory Heights  Heights Monomial Map Norm eval Cone mul 03f427722e35 construction uses the P2 M Ground Theory Heights  Heights Monomial Map Norm eval Cone mul 03f427722e35 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L16-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroBis
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
open GroundTheory.Heights₂.Heights.MonomialMapNorm
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_MonomialMapNorm_evalCone_mul_03f427722e35 (z : Cone n ℂ) (f f' : MvPolynomial (Coord n) ℤ) :
    evalCone z (f * f') = evalCone z f * evalCone z f' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MonomialMapNorm».«evalCone_mul» := P2M_GroundTheory_Heights__Heights_MonomialMapNorm_evalCone_mul_03f427722e35
