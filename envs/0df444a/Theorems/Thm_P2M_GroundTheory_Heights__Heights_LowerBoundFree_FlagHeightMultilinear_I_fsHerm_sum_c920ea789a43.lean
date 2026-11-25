-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_I_fsHerm_sum_c920ea789a43
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_I_fsHerm_sum_c920ea789a43
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:34:35.840854+00:00
-- url     : https://prove2.me/theorems/29d50962-eed0-5d58-a2ce-c0f2c410f7b7
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Flag Height Multilinear I fs Herm sum c920ea789a43: P2 M Ground Theory Heights  Heights Lower Bound Free Flag Height Multilinear I fs Herm sum c920
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Flag Height Multilinear I fs Herm sum c920ea789a43 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Flag Height Multilinear I fs Herm sum c920ea789a43 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PHFlProdLinear.lean#L128-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PHFlProdLinear.lean#L128-L135

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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} {P : Ideal (MRing ι)} {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_I_fsHerm_sum_c920ea789a43 (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) {α : Type} [Fintype α]
    (ℓ : Fin (n + 1) → α → ℤ) (x : α → K → ℤ) :
    I P (n + 1) (fun i => fsHerm ι (∑ p, ℓ i p • x p)) =
      ∑ r : Fin (n + 1) → α, (∏ i, (ℓ i (r i) : ℝ)) * I P (n + 1) (fun i => fsHerm ι (x (r i))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«FlagHeightMultilinear».«I_fsHerm_sum» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_I_fsHerm_sum_c920ea789a43
