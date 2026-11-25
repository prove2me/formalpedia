-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BoundedMonomials_exists_bound_chart_c83e86b47d1f
-- name    : P2M_GroundTheory_Heights__Heights_BoundedMonomials_exists_bound_chart_c83e86b47d1f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:16:41.318205+00:00
-- url     : https://prove2.me/theorems/fd51a78c-6be7-4775-afdb-d6d55cd0ba06
-- title:
--   P2 M Ground Theory Heights  Heights Bounded Monomials exists bound chart c83e86b47d1f: P2 M Ground Theory Heights  Heights Bounded Monomials exists bound chart c83e86b47d1f
-- statement:
--   The P2 M Ground Theory Heights  Heights Bounded Monomials exists bound chart c83e86b47d1f construction uses the P2 M Ground Theory Heights  Heights Bounded Monomials exists bound chart c83e86b47d1f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZero.lean#L166-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZero.lean#L166-L187

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

theorem P2M_GroundTheory_Heights__Heights_BoundedMonomials_exists_bound_chart_c83e86b47d1f {P : ArithVariety n} {A : HermLine n} (s : IntegralSection P A.deg)
    (c : (k : ι) → Fin (n k + 1)) :
    ∃ B : ℝ, ∀ z ∈ P.points ℂ, (∀ k, z k (c k) ≠ 0) → (∀ k i, ‖z k i‖ ≤ ‖z k (c k)‖) →
      ∀ (d : ι → ℕ) (e : MvPolynomial (Coord n) ℤ), IsChartForm P A.deg s.num s.den c d e →
        chartNorm A c d e z ≤ B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BoundedMonomials».«exists_bound_chart» := P2M_GroundTheory_Heights__Heights_BoundedMonomials_exists_bound_chart_c83e86b47d1f
