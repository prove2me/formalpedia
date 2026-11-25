-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BoundedMonomials_prod_pow_weight_36e2650dc969
-- name    : P2M_GroundTheory_Heights__Heights_BoundedMonomials_prod_pow_weight_36e2650dc969
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:18:15.674448+00:00
-- url     : https://prove2.me/theorems/d9443e8f-3842-4ff2-90c8-25e9a0b5361e
-- title:
--   P2 M Ground Theory Heights  Heights Bounded Monomials prod pow weight 36e2650dc969: P2 M Ground Theory Heights  Heights Bounded Monomials prod pow weight 36e2650dc969
-- statement:
--   The P2 M Ground Theory Heights  Heights Bounded Monomials prod pow weight 36e2650dc969 construction uses the P2 M Ground Theory Heights  Heights Bounded Monomials prod pow weight 36e2650dc969 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZero.lean#L21-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZero.lean#L21-L29

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
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_BoundedMonomials_prod_pow_weight_36e2650dc969 [Fintype ι] {F : Type*} [CommRing F] (u : ι → F) (m : Coord n →₀ ℕ) :
    (m.prod fun v e ↦ u v.1 ^ e) = ∏ k, u k ^ Finsupp.weight (coordDeg n) m k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BoundedMonomials».«prod_pow_weight» := P2M_GroundTheory_Heights__Heights_BoundedMonomials_prod_pow_weight_36e2650dc969
