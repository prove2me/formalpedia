-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartVanishing_evalHom_apply_58ec575df9f4
-- name    : P2M_GroundTheory_Heights__Heights_ChartVanishing_evalHom_apply_58ec575df9f4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:22.98039+00:00
-- url     : https://prove2.me/theorems/3f0c8001-ea7b-4c11-b233-89858e10038d
-- title:
--   P2 M Ground Theory Heights  Heights Chart Vanishing eval Hom apply 58ec575df9f4: P2 M Ground Theory Heights  Heights Chart Vanishing eval Hom apply 58ec575df9f4
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Vanishing eval Hom apply 58ec575df9f4 construction uses the P2 M Ground Theory Heights  Heights Chart Vanishing eval Hom apply 58ec575df9f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroTer.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroTer.lean#L19-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroTer
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
open GroundTheory.Heights₂.Heights.ChartVanishing
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_ChartVanishing_evalHom_apply_58ec575df9f4 {F : Type*} [CommRing F] (z : Cone n F) (f : MvPolynomial (Coord n) ℤ) :
    evalHom z f = evalCone z f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartVanishing».«evalHom_apply» := P2M_GroundTheory_Heights__Heights_ChartVanishing_evalHom_apply_58ec575df9f4
