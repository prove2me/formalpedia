-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BoundedMonomials_isCompact_unitChart_862e6b4bfb8b
-- name    : P2M_GroundTheory_Heights__Heights_BoundedMonomials_isCompact_unitChart_862e6b4bfb8b
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:16:15.969321+00:00
-- url     : https://prove2.me/theorems/e52a5f48-e86a-4b7d-8213-64b2a5be86ed
-- title:
--   P2 M Ground Theory Heights  Heights Bounded Monomials is Compact unit Chart 862e6b4bfb8b: P2 M Ground Theory Heights  Heights Bounded Monomials is Compact unit Chart 862e6b4bfb8b
-- statement:
--   The P2 M Ground Theory Heights  Heights Bounded Monomials is Compact unit Chart 862e6b4bfb8b construction uses the P2 M Ground Theory Heights  Heights Bounded Monomials is Compact unit Chart 862e6b4bfb8b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZero.lean#L131-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZero.lean#L131-L145

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

theorem P2M_GroundTheory_Heights__Heights_BoundedMonomials_isCompact_unitChart_862e6b4bfb8b (c : (k : ι) → Fin (n k + 1)) : IsCompact (unitChart c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BoundedMonomials».«isCompact_unitChart» := P2M_GroundTheory_Heights__Heights_BoundedMonomials_isCompact_unitChart_862e6b4bfb8b
