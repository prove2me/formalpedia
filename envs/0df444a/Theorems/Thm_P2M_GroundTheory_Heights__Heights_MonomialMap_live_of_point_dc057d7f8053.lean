-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMap_live_of_point_dc057d7f8053
-- name    : P2M_GroundTheory_Heights__Heights_MonomialMap_live_of_point_dc057d7f8053
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:47.587894+00:00
-- url     : https://prove2.me/theorems/52886c00-65bc-4c56-82d1-b8fe08d236c4
-- title:
--   P2 M Ground Theory Heights  Heights Monomial Map live of point dc057d7f8053: P2 M Ground Theory Heights  Heights Monomial Map live of point dc057d7f8053
-- statement:
--   The P2 M Ground Theory Heights  Heights Monomial Map live of point dc057d7f8053 construction uses the P2 M Ground Theory Heights  Heights Monomial Map live of point dc057d7f8053 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroAlt.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroAlt.lean#L34-L37

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
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_MonomialMap_live_of_point_dc057d7f8053 {P : ArithVariety n} {z : Cone n ℂ} (hz : z ∈ P.points ℂ)
    {c : (k : ι) → Fin (n k + 1)} (hc : ∀ k, z k (c k) ≠ 0) :
    ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MonomialMap».«live_of_point» := P2M_GroundTheory_Heights__Heights_MonomialMap_live_of_point_dc057d7f8053
