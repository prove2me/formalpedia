-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BoundedMonomials_exists_bound_unitChart_e84cbb7a7312
-- name    : P2M_GroundTheory_Heights__Heights_BoundedMonomials_exists_bound_unitChart_e84cbb7a7312
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:16:54.477268+00:00
-- url     : https://prove2.me/theorems/e9492a84-6eb4-4679-88f8-19bd6d4b8368
-- title:
--   P2 M Ground Theory Heights  Heights Bounded Monomials exists bound unit Chart e84cbb7a7312: P2 M Ground Theory Heights  Heights Bounded Monomials exists bound unit Chart e84cbb7a7312
-- statement:
--   The P2 M Ground Theory Heights  Heights Bounded Monomials exists bound unit Chart e84cbb7a7312 construction uses the P2 M Ground Theory Heights  Heights Bounded Monomials exists bound unit Chart e84cbb7a7312 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZero.lean#L149-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZero.lean#L149-L164

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
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_BoundedMonomials_exists_bound_unitChart_e84cbb7a7312 (A : HermLine n) (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ)
    (e : MvPolynomial (Coord n) ℤ) : ∃ B : ℝ, ∀ z ∈ unitChart c, chartNorm A c d e z ≤ B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BoundedMonomials».«exists_bound_unitChart» := P2M_GroundTheory_Heights__Heights_BoundedMonomials_exists_bound_unitChart_e84cbb7a7312
