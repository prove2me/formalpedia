-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_C_mul_prod_linForm_3831a9c346e7
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_C_mul_prod_linForm_3831a9c346e7
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:33:59.460021+00:00
-- url     : https://prove2.me/theorems/b5a5df15-c042-58f4-9d8d-e93e8f57782d
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Flag Height Multilinear C mul prod lin Form 3831a9c346e7: P2 M Ground Theory Heights  Heights Lower Bound Free Flag Height Multilinear C mul prod l
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Flag Height Multilinear C mul prod lin Form 3831a9c346e7 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Flag Height Multilinear C mul prod lin Form 3831a9c346e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PHFlProdLinear.lean#L168-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PHFlProdLinear.lean#L168-L179

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
omit [DecidableEq Ψ]

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_C_mul_prod_linForm_3831a9c346e7 (c : ℚ) {d : ℕ} (ℓ : Fin d → Ψ × Fin N → ℤ) :
    (C c * ∏ i, linForm Ψ N (ℓ i) : RootPoly Ψ N) =
      ∑ r : Fin d → Ψ × Fin N, monomial (∑ i, Finsupp.single (r i) 1) (c * ∏ i, (ℓ i (r i) : ℚ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«FlagHeightMultilinear».«C_mul_prod_linForm» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_C_mul_prod_linForm_3831a9c346e7
