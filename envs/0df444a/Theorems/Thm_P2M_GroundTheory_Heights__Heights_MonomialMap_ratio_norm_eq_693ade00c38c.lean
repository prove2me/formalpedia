-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMap_ratio_norm_eq_693ade00c38c
-- name    : P2M_GroundTheory_Heights__Heights_MonomialMap_ratio_norm_eq_693ade00c38c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:53.629942+00:00
-- url     : https://prove2.me/theorems/48f8ebcd-9907-40d7-a82e-75f328b8960d
-- title:
--   P2 M Ground Theory Heights  Heights Monomial Map ratio norm eq 693ade00c38c: P2 M Ground Theory Heights  Heights Monomial Map ratio norm eq 693ade00c38c
-- statement:
--   The P2 M Ground Theory Heights  Heights Monomial Map ratio norm eq 693ade00c38c construction uses the P2 M Ground Theory Heights  Heights Monomial Map ratio norm eq 693ade00c38c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroAlt.lean#L55-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroAlt.lean#L55-L57

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

theorem P2M_GroundTheory_Heights__Heights_MonomialMap_ratio_norm_eq_693ade00c38c {e e' x x' : ℂ} (hx : x ≠ 0) (hx' : x' ≠ 0) (h : e * x' = e' * x) (M : ℝ) :
    ‖e‖ / (‖x‖ * M) = ‖e'‖ / (‖x'‖ * M) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MonomialMap».«ratio_norm_eq» := P2M_GroundTheory_Heights__Heights_MonomialMap_ratio_norm_eq_693ade00c38c
