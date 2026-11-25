-- Prove2me | Theorems.Thm_P2M_GroundTheory_Variant__N1_norm_eval_le_of_forall_norm_le_af265dd23aa5
-- name    : P2M_GroundTheory_Variant__N1_norm_eval_le_of_forall_norm_le_af265dd23aa5
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:43:10.646151+00:00
-- url     : https://prove2.me/theorems/f01a8ea4-a7b8-4ff3-9057-b15be4f5dbf0
-- title:
--   P2 M Ground Theory Variant  N1 norm eval le of forall norm le af265dd23aa5: P2 M Ground Theory Variant  N1 norm eval le of forall norm le af265dd23aa5
-- statement:
--   The P2 M Ground Theory Variant  N1 norm eval le of forall norm le af265dd23aa5 construction uses the P2 M Ground Theory Variant  N1 norm eval le of forall norm le af265dd23aa5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/PSectionBoundedCountable.lean#L9-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/PSectionBoundedCountable.lean#L9-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_PSectionBoundedCountable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Variant₂ GroundTheory.Variant₂.N1

theorem P2M_GroundTheory_Variant__N1_norm_eval_le_of_forall_norm_le_af265dd23aa5 {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {z : (k : K) × ι k → ℂ} {c : (k : K) → ι k}
    (hz : ∀ (k : K) (i : ι k), ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c k⟩‖)
    {G : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι} {δ : K → ℕ} (hG : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog G δ) :
    ‖(MvPolynomial.eval z) ((MvPolynomial.map (Int.castRingHom ℂ)) G)‖ ≤
      coeffNorm G * ∏ k : K, ‖z ⟨k, c k⟩‖ ^ δ k := by sorry

alias «GroundTheory».«Variant₂».«N1».«norm_eval_le_of_forall_norm_le» := P2M_GroundTheory_Variant__N1_norm_eval_le_of_forall_norm_le_af265dd23aa5
