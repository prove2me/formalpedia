-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_exists_perm_toList_5fa71000ffc8
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_exists_perm_toList_5fa71000ffc8
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:34:26.236801+00:00
-- url     : https://prove2.me/theorems/3aeeef76-ebe3-514f-8c6d-d9cbeaa8ba13
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Flag Height Multilinear exists perm to List 5fa71000ffc8: P2 M Ground Theory Heights  Heights Lower Bound Free Flag Height Multilinear exists perm
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Flag Height Multilinear exists perm to List 5fa71000ffc8 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Flag Height Multilinear exists perm to List 5fa71000ffc8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PHFlProdLinear.lean#L15-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PHFlProdLinear.lean#L15-L33

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

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_exists_perm_toList_5fa71000ffc8 {α : Type} [DecidableEq α] {d : ℕ} (r : Fin d → α) :
    ∃ σ : Equiv.Perm (Fin d), ∀ (k : Fin d) (h : (k : ℕ) < (Multiset.map r Finset.univ.val).toList.length),
      (Multiset.map r Finset.univ.val).toList.get ⟨k, h⟩ = r (σ k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«FlagHeightMultilinear».«exists_perm_toList» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_exists_perm_toList_5fa71000ffc8
