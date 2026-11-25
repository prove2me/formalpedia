-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_hFl_sum_monomial_5ea69ff34fc7
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_hFl_sum_monomial_5ea69ff34fc7
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:34:32.84531+00:00
-- url     : https://prove2.me/theorems/42883ef4-9f40-5fa8-b110-0f63dfd4cb66
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Flag Height Multilinear h Fl sum monomial 5ea69ff34fc7: P2 M Ground Theory Heights  Heights Lower Bound Free Flag Height Multilinear h Fl sum monom
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Flag Height Multilinear h Fl sum monomial 5ea69ff34fc7 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Flag Height Multilinear h Fl sum monomial 5ea69ff34fc7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PHFlProdLinear.lean#L141-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PHFlProdLinear.lean#L141-L164

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsFlagGrassSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmAExpand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PHFlProdLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear
variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_hFl_sum_monomial_5ea69ff34fc7 (II : IntersectionSystem) {β : Type} (s : Finset β) (m : β → (Ψ × Fin N) →₀ ℕ)
    (a : β → ℚ) :
    hFl Ψ N II (∑ b ∈ s, monomial (m b) (a b)) = ∑ b ∈ s, (a b : ℝ) * hFlMono Ψ N II (m b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«FlagHeightMultilinear».«hFl_sum_monomial» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_hFl_sum_monomial_5ea69ff34fc7
