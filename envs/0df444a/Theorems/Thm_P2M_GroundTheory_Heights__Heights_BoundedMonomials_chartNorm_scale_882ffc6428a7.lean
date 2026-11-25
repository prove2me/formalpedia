-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BoundedMonomials_chartNorm_scale_882ffc6428a7
-- name    : P2M_GroundTheory_Heights__Heights_BoundedMonomials_chartNorm_scale_882ffc6428a7
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:16:18.461792+00:00
-- url     : https://prove2.me/theorems/1c33288c-5a70-4907-b1c4-8a65a90d8f3b
-- title:
--   P2 M Ground Theory Heights  Heights Bounded Monomials chart Norm scale 882ffc6428a7: P2 M Ground Theory Heights  Heights Bounded Monomials chart Norm scale 882ffc6428a7
-- statement:
--   The P2 M Ground Theory Heights  Heights Bounded Monomials chart Norm scale 882ffc6428a7 construction uses the P2 M Ground Theory Heights  Heights Bounded Monomials chart Norm scale 882ffc6428a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZero.lean#L102-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZero.lean#L102-L125

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

theorem P2M_GroundTheory_Heights__Heights_BoundedMonomials_chartNorm_scale_882ffc6428a7 (A : HermLine n) (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ)
    {e : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ} (he : IsWeightedHomogeneous (coordDeg n) e δ)
    (hδ : ∀ k, (δ k : ℤ) = A.deg k + d k) {u : ι → ℂ} (hu : ∀ k, u k ≠ 0) {z : Cone n ℂ}
    (hz : BlockNonzero z) :
    chartNorm A c d e (fun k i ↦ u k * z k i) = chartNorm A c d e z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BoundedMonomials».«chartNorm_scale» := P2M_GroundTheory_Heights__Heights_BoundedMonomials_chartNorm_scale_882ffc6428a7
